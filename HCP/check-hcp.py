#!/usr/bin/env python3
"""Check HCP front matter, learning-path rows, lesson anchors, and sections."""

import glob
import re
import sys
from collections import Counter
from functools import lru_cache
from pathlib import Path

REQUIRED = {
    "hcp", "id", "persona", "layer", "pull", "improvement", "concepts",
    "artifacts", "tools", "exercises", "disclosure", "owner", "state",
}
CONCEPT_KEYS = {"informal", "formal", "where"}
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
ANCHOR_REF = re.compile(r"`([A-Za-z0-9_.]+)#([A-Za-z0-9_-]+)`")
SYNOPSIS_SUBSECTIONS = [
    "Purpose",
    "PKC vocabulary in scope",
    "Verifiable properties",
    "Errors prevented",
]
VERIFIABLE_TAGS = {"type-checked", "refused", "theorem", "census", "gate"}
COMMENTED_PROBE_START = re.compile(
    r"^-- (?:(?:noncomputable|private|protected|unsafe|partial)\s+)*"
    r"(?:example|def|theorem|lemma|abbrev|structure|class|inductive|instance|#)\b"
)


class FrontMatterError(ValueError):
    def __init__(self, line, message):
        super().__init__(f"line {line}: {message}")


def parse_key_value(text, line):
    match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_-]*):(?:[ \t]+(.*))?", text)
    if not match:
        raise FrontMatterError(line, "unrecognised key-value entry")
    return match.group(1), match.group(2) or ""


def parse_scalar(value, line):
    value = value.strip()
    if not value:
        raise FrontMatterError(line, "expected a scalar value")
    if value[0] in "'\"":
        quote = value[0]
        if len(value) < 2 or value[-1] != quote:
            raise FrontMatterError(line, "unterminated quoted scalar")
        index = 1
        while index < len(value) - 1:
            if quote == "'" and value[index:index + 2] == "''":
                index += 2
            elif quote == '"' and value[index] == "\\":
                raise FrontMatterError(line, "escape sequences are unsupported")
            elif value[index] == quote:
                raise FrontMatterError(line, "unexpected text after quoted scalar")
            else:
                index += 1
        inner = value[1:-1]
        return (inner.replace("''", "'") if quote == "'" else inner), True
    if value[0] in "[{|>&*!%@`":
        raise FrontMatterError(line, "unsupported scalar syntax")
    return value, False


def parse_inline_list(value, line):
    if not value.endswith("]"):
        raise FrontMatterError(line, "unterminated inline list")
    inner = value[1:-1]
    if not inner.strip():
        return []

    items = []
    start = 0
    quote = None
    index = 0
    while index < len(inner):
        char = inner[index]
        if quote:
            if quote == "'" and inner[index:index + 2] == "''":
                index += 2
                continue
            if quote == '"' and char == "\\":
                raise FrontMatterError(line, "escape sequences are unsupported")
            if char == quote:
                quote = None
        elif char in "'\"":
            quote = char
        elif char == ",":
            items.append(inner[start:index].strip())
            start = index + 1
        elif char in "[]{}":
            raise FrontMatterError(line, "nested inline collections are unsupported")
        index += 1

    if quote:
        raise FrontMatterError(line, "unterminated quoted list item")
    items.append(inner[start:].strip())
    if any(not item for item in items):
        raise FrontMatterError(line, "empty inline-list item")
    return [parse_scalar(item, line)[0] for item in items]


def parse_value(value, line):
    value = value.strip()
    if value.startswith("["):
        return parse_inline_list(value, line), False
    if value.startswith("]"):
        raise FrontMatterError(line, "unexpected closing bracket")
    return parse_scalar(value, line)


def indentation(line, number):
    prefix = line[:len(line) - len(line.lstrip(" \t"))]
    if "\t" in prefix:
        raise FrontMatterError(number, "tabs are unsupported in indentation")
    return len(prefix)


def add_mapping_value(mapping, key, value, line):
    if key in mapping:
        raise FrontMatterError(line, f"duplicate key '{key}'")
    mapping[key] = value


def parse_block(lines, start, key_line):
    index = start
    while index < len(lines) and not lines[index][1].strip():
        index += 1
    if index == len(lines):
        raise FrontMatterError(key_line, "expected an indented mapping or list")

    number, first = lines[index]
    if indentation(first, number) != 2:
        raise FrontMatterError(number, "expected two spaces of indentation")

    if first[2:].startswith("- "):
        items = []
        current = None
        while index < len(lines):
            number, line = lines[index]
            if not line.strip():
                index += 1
                continue
            spaces = indentation(line, number)
            if spaces == 0:
                break
            if spaces == 2 and line[2:].startswith("- "):
                if current is not None:
                    items.append(current)
                current = {}
                item_key, item_value = parse_key_value(line[4:], number)
                value, _ = parse_value(item_value, number)
                add_mapping_value(current, item_key, value, number)
            elif spaces == 4 and current is not None:
                item_key, item_value = parse_key_value(line[4:], number)
                value, _ = parse_value(item_value, number)
                add_mapping_value(current, item_key, value, number)
            else:
                raise FrontMatterError(number, "unexpected indentation or block-list item")
            index += 1
        if current is not None:
            items.append(current)
        return items, index

    mapping = {}
    while index < len(lines):
        number, line = lines[index]
        if not line.strip():
            index += 1
            continue
        spaces = indentation(line, number)
        if spaces == 0:
            break
        if spaces != 2 or line[2:].startswith("- "):
            raise FrontMatterError(number, "unexpected indentation in mapping")
        child_key, child_value = parse_key_value(line[2:], number)
        value, _ = parse_value(child_value, number)
        add_mapping_value(mapping, child_key, value, number)
        index += 1
    if not mapping:
        raise FrontMatterError(key_line, "expected an indented mapping")
    return mapping, index


def parse_front_matter(text) -> dict:
    lines = text.splitlines()
    if not lines or lines[0] != "---":
        raise FrontMatterError(1, "missing opening delimiter")
    end = next((index for index, line in enumerate(lines[1:], start=1)
                if line == "---"), None)
    if end is None:
        raise FrontMatterError(len(lines), "missing closing delimiter")

    content = list(enumerate(lines[1:end], start=2))
    data = {}
    index = 0
    while index < len(content):
        number, line = content[index]
        if not line.strip():
            index += 1
            continue
        if indentation(line, number) != 0:
            raise FrontMatterError(number, "unexpected top-level indentation")
        key, raw_value = parse_key_value(line, number)
        if key in data:
            raise FrontMatterError(number, f"duplicate key '{key}'")
        index += 1
        if not raw_value.strip():
            data[key], index = parse_block(content, index, number)
        else:
            value, quoted = parse_value(raw_value, number)
            if key in {"hcp", "exercises"} and not quoted and isinstance(value, str) and value.isdigit():
                value = int(value)
            data[key] = value
    return data


def heading_section(text, level, title):
    hashes = "#" * level
    pattern = re.compile(rf"(?m)^{re.escape(hashes)} {re.escape(title)}[ \t]*$")
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        return None
    end_pattern = re.compile(rf"(?m)^{re.escape(hashes)} (?!#).+$")
    following = end_pattern.search(text, matches[0].end())
    return text[matches[0].start():following.start() if following else len(text)]


def chapter_synopsis_section(text):
    metadata = re.search(r"(?ms)^%%%[ \t]*\n.*?^%%%[ \t]*$", text)
    if metadata is None:
        return None

    body = text[metadata.end():]
    headings = list(re.finditer(r"(?m)^# (?!#).*$", body))
    if not headings or not re.fullmatch(r"# Synopsis[ \t]*", headings[0].group()):
        return None
    synopsis_headings = [
        match for match in headings
        if re.fullmatch(r"# Synopsis[ \t]*", match.group())
    ]
    if len(synopsis_headings) != 1:
        return None

    start = metadata.end() + headings[0].start()
    end = (
        metadata.end() + headings[1].start()
        if len(headings) > 1
        else len(text)
    )
    return text[start:end]


def normalized_synopsis(section, shift_headings=False):
    if section is None:
        return None
    if shift_headings:
        section = re.sub(r"(?m)^## Synopsis[ \t]*$", "# Synopsis", section)
        section = re.sub(r"(?m)^### ", "## ", section)
    return re.sub(r"\s+", " ", section).strip()


def vocabulary_name(term):
    if term.startswith("#"):
        return term, True
    if term.startswith("@[") and term.endswith("]"):
        return term[2:-1], False
    return term, False


def contains_identifier(source, name):
    return re.search(
        r"(?<!\w)" + re.escape(name) + r"(?!\w)", source
    ) is not None


@lru_cache(maxsize=1)
def vocabulary_sources():
    paths = []
    for directory in ("PropertyKindCalculus", "ForPhysLib"):
        paths.extend((ROOT / directory).rglob("*.lean"))
    return tuple(
        (path, path.read_text(encoding="utf-8"))
        for path in sorted(paths)
        if path.is_file()
    )


def declaration_in_namespace(source, namespace, member):
    namespace_stack = []
    lines = source.splitlines()
    for index, line in enumerate(lines):
        opened = re.match(r"^\s*namespace\s+([A-Za-z_][\w.]*)\s*$", line)
        if opened:
            namespace_stack.append(opened.group(1))
            continue
        closed = re.match(r"^\s*end(?:\s+([A-Za-z_][\w.]*))?\s*$", line)
        if closed:
            if namespace_stack:
                name = closed.group(1)
                if name is None:
                    namespace_stack.pop()
                else:
                    while namespace_stack:
                        current = namespace_stack.pop()
                        if current == name or current.endswith("." + name):
                            break
            continue

        namespace_here = ".".join(namespace_stack)
        matches_namespace = (
            namespace_here == namespace
            or namespace_here.endswith("." + namespace)
        )
        declaration = re.match(
            r"^\s*(?:(?:private|protected|noncomputable)\s+)*"
            r"(?:def|theorem|lemma|abbrev|structure|class|inductive|instance)"
            r"\s+([A-Za-z_][\w'.]*)\b",
            line,
        )
        if matches_namespace and declaration and declaration.group(1) == member:
            return True

        aggregate = re.match(
            r"^(\s*)(?:(?:private|protected|noncomputable)\s+)*"
            r"(?:structure|class|inductive)\s+([A-Za-z_][\w'.]*)\b.*\bwhere\s*$",
            line,
        )
        if not aggregate:
            continue
        aggregate_name = aggregate.group(2)
        if namespace_here:
            aggregate_name = f"{namespace_here}.{aggregate_name}"
        if (
            aggregate_name != namespace
            and not aggregate_name.endswith("." + namespace)
        ):
            continue
        base_indent = len(aggregate.group(1))
        for field_line in lines[index + 1:]:
            if not field_line.strip():
                continue
            indent = len(field_line) - len(field_line.lstrip(" \t"))
            if indent <= base_indent:
                break
            field = re.match(r"^\s*(?:\|\s*)?([A-Za-z_][\w']*)\s*(?::|\b)", field_line)
            if field and field.group(1) == member:
                return True
    return False


def contains_vocabulary_name(source, term):
    name, command = vocabulary_name(term)
    if not name:
        return False
    if command:
        return re.search(
            r"(?<![\w#])" + re.escape(name) + r"(?!\w)", source
        ) is not None
    if term.startswith("@[") and term.endswith("]"):
        return contains_identifier(source, name)
    if "." not in name:
        return contains_identifier(source, name)
    if contains_identifier(source, name):
        return True

    namespace, member = name.rsplit(".", 1)
    if not contains_identifier(source, member):
        return False

    # Dot-notation members may occur unqualified at use sites, so validate their declaration namespace.
    for _, candidate in vocabulary_sources():
        if contains_identifier(candidate, name):
            return True
        if declaration_in_namespace(candidate, namespace, member):
            return True
    return False


def synopsis_bullets(path, section, label, errors):
    bullets = []
    for line in section.splitlines()[1:]:
        if not line.strip():
            continue
        if line.startswith("- "):
            bullets.append(line[2:].strip())
        elif line.startswith(("  ", "\t")) and bullets:
            bullets[-1] += " " + line.strip()
        else:
            errors.append(
                f"{path}: {label} contains a non-bullet line: {line.strip()!r}"
            )
    if not bullets:
        errors.append(f"{path}: {label} must contain at least one bullet")
    return bullets


def synopsis_errors(path, text, data):
    errors = []
    section_titles = re.findall(r"(?m)^## (.+?)\s*$", text)
    if not section_titles or section_titles[0] != "Synopsis":
        errors.append(f"{path}: '## Synopsis' must be the first level-2 section")
    if section_titles.count("Synopsis") != 1:
        errors.append(f"{path}: expected exactly one '## Synopsis' section")

    synopsis = heading_section(text, 2, "Synopsis")
    if synopsis is None:
        errors.append(f"{path}: missing or duplicate '## Synopsis' section")
    else:
        subsections = list(re.finditer(r"(?m)^### (.+?)\s*$", synopsis))
        names = [match.group(1) for match in subsections]
        if names != SYNOPSIS_SUBSECTIONS:
            errors.append(
                f"{path}: Synopsis subsections must be exactly "
                f"{SYNOPSIS_SUBSECTIONS} in order"
            )
        for index, match in enumerate(subsections):
            end = subsections[index + 1].start() if index + 1 < len(subsections) else len(synopsis)
            if not synopsis[match.end():end].strip():
                errors.append(f"{path}: Synopsis subsection '{match.group(1)}' is empty")

        lesson_path = None
        vocab = heading_section(synopsis, 3, "PKC vocabulary in scope")
        if vocab is None:
            errors.append(f"{path}: missing or duplicate 'PKC vocabulary in scope' subsection")
        else:
            new_list = re.search(r"(?m)^New at this step:[ \t]*$", vocab)
            if not new_list:
                errors.append(f"{path}: vocabulary section is missing 'New at this step:'")
            elif not re.search(r"(?m)^- .+", vocab[new_list.end():]):
                errors.append(f"{path}: 'New at this step:' must be followed by a list")

            lesson_number = data.get("hcp")
            if type(lesson_number) is int and 1 <= lesson_number <= 7:
                candidates = sorted(HERE.glob(f"L{lesson_number - 1}_*.lean"))
                if len(candidates) == 1:
                    lesson_path = candidates[0]
            if lesson_path is None:
                errors.append(f"{path}: could not map card to its HCP/Lk_*.lean lesson")
            else:
                lesson = lesson_path.read_text(encoding="utf-8")
                for term in re.findall(r"`([^`]+)`", vocab):
                    if not contains_vocabulary_name(lesson, term):
                        errors.append(
                            f"{path}: vocabulary term '{term}' not found in {lesson_path.name}"
                        )

        verifiable = heading_section(synopsis, 3, "Verifiable properties")
        if verifiable is not None:
            bullets = synopsis_bullets(path, verifiable, "Verifiable properties", errors)
            for index, bullet in enumerate(bullets, 1):
                tags = list(re.finditer(r"\(([a-z-]+)\)", bullet))
                first_ref = ANCHOR_REF.search(bullet)
                tag_is_before_ref = (
                    len(tags) == 1
                    and first_ref is not None
                    and tags[0].end() <= first_ref.start()
                    and not bullet[tags[0].end():first_ref.start()].strip()
                )
                if (
                    len(tags) != 1
                    or tags[0].group(1) not in VERIFIABLE_TAGS
                    or not tag_is_before_ref
                ):
                    errors.append(
                        f"{path}: Verifiable-properties bullet {index} must have exactly one "
                        f"parenthesized lowercase tag from {sorted(VERIFIABLE_TAGS)} "
                        "immediately before its first Module#anchor ref"
                    )
                if first_ref is None:
                    errors.append(
                        f"{path}: Verifiable-properties bullet {index} is missing a Module#anchor ref"
                    )

        prevented = heading_section(synopsis, 3, "Errors prevented")
        if prevented is not None:
            bullets = synopsis_bullets(path, prevented, "Errors prevented", errors)
            for index, bullet in enumerate(bullets, 1):
                if not ANCHOR_REF.search(bullet):
                    errors.append(
                        f"{path}: Errors-prevented bullet {index} is missing a Module#anchor ref"
                    )

        if lesson_path is not None:
            chapter_path = (
                ROOT / "blueprint" / "PropertyKindCalculusBlueprint" / "Chapters" /
                "HCP" / lesson_path.name
            )
            if not chapter_path.is_file():
                errors.append(f"{path}: matching Synopsis chapter not found at {chapter_path}")
            else:
                chapter_text = chapter_path.read_text(encoding="utf-8")
                chapter_section = chapter_synopsis_section(chapter_text)
                if chapter_section is None:
                    errors.append(
                        f"{path}: matching chapter is missing, duplicates, or does not start "
                        "with '# Synopsis' after %%% metadata"
                    )
                elif normalized_synopsis(synopsis, True) != normalized_synopsis(chapter_section):
                    errors.append(f"{path}: Synopsis differs from the matching chapter")
    return errors


def check(path):
    text = path.read_text(encoding="utf-8")
    errors = []
    if not text.startswith("---\n") or "\n---\n" not in text[4:]:
        return [f"{path}: missing or unterminated YAML front matter"]
    try:
        data = parse_front_matter(text)
    except FrontMatterError as exc:
        return [f"{path}: {exc}"]
    if not isinstance(data, dict):
        return [f"{path}: front matter is not a mapping"]
    errors.extend(f"{path}: missing field '{key}'" for key in sorted(REQUIRED - data.keys()))
    expected_id = path.stem.lower()
    if data.get("id") != expected_id:
        errors.append(f"{path}: id '{data.get('id')}' does not match file name '{expected_id}'")
    concepts = data.get("concepts")
    if not isinstance(concepts, list) or not concepts:
        errors.append(f"{path}: concepts must be a non-empty list")
    else:
        for i, concept in enumerate(concepts):
            if not isinstance(concept, dict) or set(concept) != CONCEPT_KEYS:
                errors.append(f"{path}: concepts[{i}] must have exactly {sorted(CONCEPT_KEYS)}")
    state = data.get("state")
    if not isinstance(state, dict) or not isinstance(state.get("completed"), list):
        errors.append(f"{path}: state.completed must be a list")
    titles = set(re.findall(r"^## (.+)$", text, re.M))
    if "Synopsis" not in titles:
        errors.append(f"{path}: missing section 'Synopsis'")
    for number, title in enumerate(
        ["Persona", "Pull", "Small rigorous improvement", "Learning path",
         "AI assistance contract", "Questions to ask the model so far",
         "System-context card"], 1
    ):
        if f"{number}. {title}" not in titles:
            errors.append(f"{path}: missing section '{number}. {title}'")
    errors.extend(synopsis_errors(path, text, data))
    learning = text.split("\n## 4. Learning path", 1)
    rows = []
    if len(learning) == 2:
        rows = [line for line in learning[1].split("\n## 5.", 1)[0].splitlines()
                if re.match(r"\|\s*\d+\s*\|", line)]
    exercises = data.get("exercises")
    if type(exercises) is not int or exercises != len(rows):
        errors.append(f"{path}: front matter says {exercises} exercises, learning path has {len(rows)}")
    errors.extend(worksheet_errors(path, text, data))
    for module, anchor in ANCHOR_REF.findall(text):
        lesson = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if not lesson.is_file():
            errors.append(f"{path}: checked-by module '{module}' not found at {lesson}")
        elif not re.search(rf"^\s*--\s*ANCHOR:\s*{re.escape(anchor)}\s*$",
                           lesson.read_text(encoding="utf-8"), re.M):
            errors.append(f"{path}: anchor '{anchor}' not found in {lesson}")
    return errors


def normalize_probe_line(line):
    return " ".join(line.split())


def error_guard_commands(block):
    guards = list(re.finditer(r"(?m)^[ \t]*#guard_msgs\b([^\r\n]*)", block))
    commands = []
    previous_end = 0
    for index, guard in enumerate(guards):
        if re.search(r"\berror:", block[previous_end:guard.start()]):
            inline = re.search(r"\bin\b(.*)$", guard.group(1))
            command_lines = []
            inline_command = inline.group(1).strip() if inline else ""
            if inline_command:
                command_lines.append(inline_command)
            next_guard = guards[index + 1].start() if index + 1 < len(guards) else len(block)
            for line in block[guard.end():next_guard].splitlines():
                if not line.strip():
                    if command_lines:
                        break
                    continue
                if re.match(r"^[ \t]*#guard_msgs\b", line):
                    break
                command_lines.append(line.strip())
            commands.append([normalize_probe_line(line) for line in command_lines] or ["<empty command>"])
        previous_end = guard.end()
    return commands


def commented_probe_commands(block):
    probes = []
    current = []

    def finish_probe():
        if current:
            probes.append([normalize_probe_line(line) for line in current])
            current.clear()

    for line in block.splitlines():
        if line.startswith("-- EXERCISE:") or line.startswith("-- EXERCISE_END:"):
            finish_probe()
        elif line.startswith("-- @["):
            finish_probe()
        elif COMMENTED_PROBE_START.match(line):
            finish_probe()
            current.append(line[3:])
        elif current and line.startswith("-- "):
            current.append(line[3:])
        else:
            finish_probe()
    finish_probe()
    return probes


EXAMPLE_DECLARATION = re.compile(
    r"^\s*(?:#guard_msgs\b.*?\bin\s+)?(?:noncomputable\s+)?example\b"
)
EXAMPLE_MARKERS = (
    "-- ANCHOR:", "-- ANCHOR_END:", "-- EXERCISE:", "-- EXERCISE_END:",
    "-- TODO:", "-- GIVEN:",
)


def example_comment_errors(path, text):
    errors = []
    lines = text.splitlines()
    for index, line in enumerate(lines):
        if not EXAMPLE_DECLARATION.match(line):
            continue

        preceding = index - 1
        if not line.lstrip().startswith("#guard_msgs"):
            while preceding >= 0 and lines[preceding].lstrip().startswith("#guard_msgs"):
                preceding -= 1

        if preceding >= 0 and lines[preceding].rstrip().endswith("-/"):
            while preceding >= 0 and "/--" not in lines[preceding]:
                preceding -= 1
            if preceding >= 0:
                preceding -= 1

        preceding_line = lines[preceding].lstrip() if preceding >= 0 else ""
        has_comment = (
            preceding_line.startswith("-- ")
            and not preceding_line.startswith(EXAMPLE_MARKERS)
        )
        if not has_comment:
            errors.append(
                f"{path}:{index + 1}: example has no preceding comment saying what it shows"
            )
    return errors


def worksheet_errors(path, text, data):
    errors = []
    lesson_number = data.get("hcp")
    if type(lesson_number) is not int or not 1 <= lesson_number <= 7:
        errors.append(f"{path}: could not map card to its HCP lesson worksheet")
        return errors

    candidates = sorted(HERE.glob(f"L{lesson_number - 1}_*.lean"))
    if len(candidates) != 1:
        errors.append(f"{path}: could not map card to its HCP/Lk_*.lean solution")
        return errors

    solution_path = candidates[0]
    worksheet_path = HERE / "Worksheets" / solution_path.name
    if not worksheet_path.is_file():
        errors.append(f"{path}: worksheet not found at {worksheet_path}")
        worksheet_text = ""
    else:
        worksheet_text = worksheet_path.read_text(encoding="utf-8")

    solution = solution_path.read_text(encoding="utf-8")
    errors.extend(example_comment_errors(solution_path, solution))
    errors.extend(example_comment_errors(worksheet_path, worksheet_text))
    anchor_pattern = re.compile(r"(?m)^-- ANCHOR: ([A-Za-z0-9_-]+)[ \t]*$")
    anchor_end_pattern = re.compile(r"(?m)^-- ANCHOR_END: ([A-Za-z0-9_-]+)[ \t]*$")
    anchor_matches = list(anchor_pattern.finditer(solution))
    anchors = [match.group(1) for match in anchor_matches]
    anchor_blocks = {}
    for anchor in anchor_matches:
        name = anchor.group(1)
        end = next(
            (match for match in anchor_end_pattern.finditer(solution, anchor.end())
             if match.group(1) == name),
            None,
        )
        if end is not None:
            anchor_blocks[name] = solution[anchor.end():end.start()]

    exercises = list(re.finditer(
        r"(?m)^-- EXERCISE: ([A-Za-z0-9_-]+)[ \t]*$", worksheet_text
    ))
    exercise_names = [match.group(1) for match in exercises]
    if exercise_names != anchors:
        errors.append(
            f"{path}: worksheet EXERCISE names do not match solution ANCHOR names in order"
        )

    end_pattern = re.compile(r"(?m)^-- EXERCISE_END: ([A-Za-z0-9_-]+)[ \t]*$")
    for index, exercise in enumerate(exercises):
        next_start = exercises[index + 1].start() if index + 1 < len(exercises) else len(worksheet_text)
        ends = [match for match in end_pattern.finditer(worksheet_text, exercise.end(), next_start)]
        matching_end = next((match for match in ends if match.group(1) == exercise.group(1)), None)
        if matching_end is None:
            errors.append(
                f"{path}: exercise '{exercise.group(1)}' is missing its matching EXERCISE_END"
            )
            block = worksheet_text[exercise.start():next_start]
        else:
            block = worksheet_text[exercise.start():matching_end.end()]
        if "TODO:" not in block:
            errors.append(f"{path}: exercise '{exercise.group(1)}' is missing a TODO")
        error_commands = error_guard_commands(anchor_blocks.get(exercise.group(1), ""))
        first_lines = [
            command[0] if command else "<empty command>" for command in error_commands
        ]
        duplicate_first_lines = Counter(first_lines)
        seen_first_lines = Counter()
        occurrences = []
        for first_line in first_lines:
            seen_first_lines[first_line] += 1
            occurrences.append(seen_first_lines[first_line])

        worksheet_commands = commented_probe_commands(block)
        unconsumed = [True] * len(worksheet_commands)
        missing = []
        command_order = sorted(
            range(len(error_commands)),
            key=lambda index: (-len(error_commands[index]), index),
        )
        for command_index in command_order:
            command = error_commands[command_index]
            for probe_index, probe in enumerate(worksheet_commands):
                if (unconsumed[probe_index] and len(probe) >= len(command)
                        and probe[:len(command)] == command):
                    unconsumed[probe_index] = False
                    break
            else:
                missing.append(command_index)

        for command_index in sorted(missing):
            first_line = first_lines[command_index]
            occurrence = (
                f" (occurrence {occurrences[command_index]})"
                if duplicate_first_lines[first_line] > 1
                else ""
            )
            errors.append(
                f"{path}: exercise '{exercise.group(1)}' is missing a commented "
                f"counterpart for guarded command '{first_line}{occurrence}'"
            )

    if "#guard_msgs" in worksheet_text:
        errors.append(f"{path}: worksheet must not contain #guard_msgs")

    expected_line = (
        f"Worksheet: `HCP/Worksheets/{solution_path.name}` · "
        f"Solution: `HCP/{solution_path.name}`"
    )
    learning = text.split("\n## 4. Learning path", 1)
    learning_section = learning[1].split("\n## 5.", 1)[0] if len(learning) == 2 else ""
    if expected_line not in learning_section:
        errors.append(f"{path}: Learning path is missing '{expected_line}'")
    return errors


def main():
    paths = sorted(Path(p) for p in glob.glob(str(HERE / "*.md"))
                   if not p.endswith("README.md"))
    if not paths:
        print("no HCPs found", file=sys.stderr)
        return 1
    errors = [error for path in paths for error in check(path)]
    for error in errors:
        print(error, file=sys.stderr)
    print(f"{len(paths)} HCPs checked, {len(errors)} errors")
    return bool(errors)


if __name__ == "__main__":
    sys.exit(main())
