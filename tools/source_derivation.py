"""Reconstruct the reviewed local diagnostic extension from exact source bytes."""
from __future__ import annotations

import hashlib
from pathlib import Path
import re

PATCH_PATH = "reference/binding-trace.patch"
MAIN = "\nfn main() {"
HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@(?:[^\n]*)\n$")


def digest(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def apply_exact_patch(source: str, patch: str) -> str:
    """Apply only an exact, single-file unified diff; no fuzzy context or paths."""
    lines = patch.splitlines(keepends=True)
    if lines[:2] != ["--- a/reference/checker.goose\n", "+++ b/reference/checker.goose\n"]:
        raise ValueError("diagnostic patch must name exactly the owned checker file")
    original = source.splitlines(keepends=True)
    output: list[str] = []
    old_cursor, index, hunks = 0, 2, 0
    while index < len(lines):
        match = HUNK.fullmatch(lines[index])
        if match is None:
            raise ValueError("unsupported diagnostic patch header")
        old_start, old_count, new_start, new_count = match.groups()
        old_count, new_count = int(old_count or 1), int(new_count or 1)
        start = int(old_start) - (1 if old_count else 0)
        new_offset = int(new_start) - (1 if new_count else 0)
        if start < old_cursor or start > len(original):
            raise ValueError("diagnostic patch has overlapping or escaping context")
        output.extend(original[old_cursor:start])
        if len(output) != new_offset:
            raise ValueError("diagnostic patch output offset differs from its header")
        old_cursor, consumed, produced = start, 0, 0
        index += 1
        while index < len(lines) and not lines[index].startswith("@@ "):
            line = lines[index]
            if not line.endswith("\n") or line[0] not in " +-":
                raise ValueError("unsupported diagnostic patch content")
            tag, text = line[0], line[1:]
            if tag in " -":
                if old_cursor >= len(original) or original[old_cursor] != text:
                    raise ValueError("diagnostic patch context differs from the pinned base")
                old_cursor += 1
                consumed += 1
            if tag in " +":
                output.append(text)
                produced += 1
            index += 1
        if (consumed, produced) != (old_count, new_count):
            raise ValueError("diagnostic patch hunk lengths are inconsistent")
        hunks += 1
    if hunks == 0:
        raise ValueError("diagnostic patch contains no reviewed change")
    output.extend(original[old_cursor:])
    return "".join(output)


def reconstruct(root: Path, base: str, extension: dict) -> tuple[str, dict]:
    if extension.get("path") != PATCH_PATH or extension.get("base_derivative_sha256") != digest(base):
        raise ValueError("diagnostic extension differs from the pinned local derivative")
    path = root / PATCH_PATH
    if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError("diagnostic patch must remain an owned file")
    patch = path.read_bytes().decode("utf-8")
    if extension.get("sha256") != digest(patch):
        raise ValueError("diagnostic patch differs from its recorded digest")
    result = apply_exact_patch(base, patch)
    if base.count(MAIN) != 1 or result.count(MAIN) != 1:
        raise ValueError("diagnostic extension has an ambiguous main boundary")
    prefix = base.split(MAIN, 1)[0] + "\n"
    if not result.startswith(prefix) or extension.get("preserved_checker_prefix_sha256") != digest(prefix):
        raise ValueError("diagnostic extension changed the checking or parser function prefix")
    return result, {"path": PATCH_PATH, "sha256": digest(patch),
                    "base_derivative_sha256": digest(base),
                    "preserved_checker_prefix_sha256": digest(prefix),
                    "checking_and_parser_function_prefix_unchanged": True}
