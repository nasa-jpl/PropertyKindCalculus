#!/usr/bin/env python3
"""Check HCP front matter, learning-path rows, lesson anchors, and sections."""

import glob
import re
import sys
from pathlib import Path

REQUIRED = {
    "hcp", "id", "persona", "layer", "pull", "improvement", "concepts",
    "artifacts", "tools", "exercises", "disclosure", "owner", "state",
}
CONCEPT_KEYS = {"informal", "formal", "where"}
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
ANCHOR_REF = re.compile(r"`([A-Za-z0-9_.]+)#([A-Za-z0-9_-]+)`")


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
    for number, title in enumerate(
        ["Persona", "Pull", "Small rigorous improvement", "Learning path",
         "AI assistance contract", "Questions to ask the model so far",
         "System-context card"], 1
    ):
        if f"{number}. {title}" not in titles:
            errors.append(f"{path}: missing section '{number}. {title}'")
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


def error_guard_count(block):
    guards = list(re.finditer(r"(?m)^[ \t]*#guard_msgs\b", block))
    count = 0
    previous_end = 0
    for guard in guards:
        if re.search(r"\berror:", block[previous_end:guard.start()]):
            count += 1
        previous_end = guard.end()
    return count


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
        error_pins = error_guard_count(anchor_blocks.get(exercise.group(1), ""))
        commented_probes = sum(
            bool(re.match(r"^-- (?:example|def|theorem|#)", line))
            for line in block.splitlines()
        )
        if error_pins > commented_probes:
            errors.append(
                f"{path}: exercise '{exercise.group(1)}' has {commented_probes} "
                f"commented probe starts for {error_pins} error #guard_msgs blocks"
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
