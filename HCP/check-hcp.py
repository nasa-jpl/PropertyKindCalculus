#!/usr/bin/env python3
"""Check HCP front matter, learning-path rows, lesson anchors, and sections."""

import glob
import re
import sys
from pathlib import Path

import yaml

REQUIRED = {
    "hcp", "id", "persona", "layer", "pull", "improvement", "concepts",
    "artifacts", "tools", "exercises", "disclosure", "owner", "state",
}
CONCEPT_KEYS = {"informal", "formal", "where"}
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
ANCHOR_REF = re.compile(r"`([A-Za-z0-9_.]+)#([A-Za-z0-9_-]+)`")


def check(path):
    text = path.read_text(encoding="utf-8")
    errors = []
    if not text.startswith("---\n") or "\n---\n" not in text[4:]:
        return [f"{path}: missing or unterminated YAML front matter"]
    try:
        data = yaml.safe_load(text[4:].split("\n---\n", 1)[0])
    except yaml.YAMLError as exc:
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
    for module, anchor in ANCHOR_REF.findall(text):
        lesson = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if not lesson.is_file():
            errors.append(f"{path}: checked-by module '{module}' not found at {lesson}")
        elif not re.search(rf"^\s*--\s*ANCHOR:\s*{re.escape(anchor)}\s*$",
                           lesson.read_text(encoding="utf-8"), re.M):
            errors.append(f"{path}: anchor '{anchor}' not found in {lesson}")
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
