#!/usr/bin/env python3
"""Replay the bounded stored-binding profile through the actual Quint evaluator.

Input: nonempty kind,name,target,level;... traces of length at most three from
fourteen declared actions. Quint evaluates all 2,954 profile traces. This
adapter checks their identities and decodes length-framed payload vectors;
it implements no definition-checking or state-transition semantics.
"""
from __future__ import annotations

import itertools
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ACTIONS = (
    (0, 0, 0, 0), (0, 1, 0, 0), (1, 0, 0, 0), (1, 1, 0, 0),
    (2, 0, 0, 0), (2, 0, 1, 0), (2, 1, 0, 0), (2, 1, 1, 0),
    (3, 0, 0, 0), (3, 1, 0, 0), (0, 0, 0, 1), (0, 1, 0, 1),
    (2, 0, 1, 1), (2, 1, 0, 1),
)
PROFILE = {trace for length in (1, 2, 3) for trace in itertools.product(ACTIONS, repeat=length)}


def trace_key(line: str) -> tuple[tuple[int, ...], ...]:
    if not re.fullmatch(r"[0-3],[01],[01],[01](?:;[0-3],[01],[01],[01]){0,2}", line):
        raise ValueError("trace is outside the three-step, two-name, two-level profile")
    trace = tuple(tuple(int(value) for value in item.split(",")) for item in line.split(";"))
    if trace not in PROFILE:
        raise ValueError("trace contains an action outside the fourteen-action profile")
    return trace


class Wire:
    """Read only numeric framing emitted by StoredBindings.wire."""

    def __init__(self, values: object):
        if not isinstance(values, list) or any(type(value) is not int or value < 0 for value in values):
            raise ValueError("Quint returned a nonnegative-integer wire vector with invalid fields")
        self.values = values
        self.position = 0

    def number(self) -> int:
        if self.position >= len(self.values):
            raise ValueError("Quint returned a truncated stored-binding wire vector")
        value = self.values[self.position]
        self.position += 1
        return value

    def vector(self) -> list[int]:
        length = self.number()
        if length > len(self.values) - self.position:
            raise ValueError("Quint returned a truncated expression vector")
        value = self.values[self.position:self.position + length]
        self.position += length
        return value

    def binding(self) -> dict:
        return {"name": self.number(), "type": self.vector(), "value": self.vector(), "inferred": self.vector()}

    def environment(self) -> list[dict]:
        count = self.number()
        if count > (len(self.values) - self.position) // 4:
            raise ValueError("Quint returned an impossible binding inventory length")
        return [self.binding() for _ in range(count)]

    def observation(self) -> dict:
        halted, authority = self.number(), self.number()
        if halted not in (0, 1) or authority not in (0, 1):
            raise ValueError("Quint returned invalid Boolean flags")
        environment = self.environment()
        count = self.number()
        if count > (len(self.values) - self.position) // 2:
            raise ValueError("Quint returned an impossible outcome inventory length")
        outcomes = [{"name": self.number(), "code": self.number()} for _ in range(count)]
        count = self.number()
        if count > (len(self.values) - self.position) // 3:
            raise ValueError("Quint returned an impossible snapshot inventory length")
        snapshots = [{"name": self.number(), "code": self.number(), "environment": self.environment()}
                     for _ in range(count)]
        if self.position != len(self.values):
            raise ValueError("Quint returned trailing stored-binding wire data")
        return {"halted": bool(halted), "environment": environment, "outcomes": outcomes,
                "successes": len(environment), "acceptance_authority": bool(authority), "snapshots": snapshots}


def decode_profile(text: str) -> dict:
    values = json.loads(text)
    if not isinstance(values, list) or len(values) != len(PROFILE):
        raise ValueError("Quint did not return the complete 2,954-case stored-binding profile")
    decoded = {}
    for value in values:
        if not isinstance(value, list) or not value or type(value[0]) is not int or value[0] not in (1, 2, 3):
            raise ValueError("Quint returned invalid stored-binding trace framing")
        length = value[0]
        if len(value) < 1 + 4 * length:
            raise ValueError("Quint returned a truncated stored-binding trace identity")
        fields = value[1:1 + 4 * length]
        if any(type(item) is not int for item in fields):
            raise ValueError("Quint returned a nonintegral stored-binding trace identity")
        trace = tuple(tuple(fields[i:i + 4]) for i in range(0, len(fields), 4))
        if trace not in PROFILE or trace in decoded:
            raise ValueError("Quint returned an unknown or duplicate stored-binding trace identity")
        decoded[trace] = Wire(value[1 + 4 * length:]).observation()
    if set(decoded) != PROFILE:
        raise ValueError("Quint omitted a required stored-binding trace")
    return decoded


def main() -> int:
    lines = sys.stdin.read().splitlines()
    if not lines or any(not line for line in lines):
        raise ValueError("at least one nonempty stored-binding trace is required")
    requested = [trace_key(line) for line in lines]
    name = os.environ.get("QUINT", str(HERE / "node_modules/.bin/quint"))
    quint = shutil.which(name)
    if quint is None:
        raise ValueError("missing Quint executable")
    # Quint's REPL can exit at EOF before a large pipe-backed stdout buffer is
    # drained. A regular temporary output file gives the CLI synchronous writes
    # and lets us validate the complete profile before emitting any observation.
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8") as stdout:
        result = subprocess.run(
            [quint, "repl", "--require", str(HERE / "StoredBindings.qnt") + "::StoredBindings",
             "--backend=typescript", "--quiet"],
            input="replayProfile\n", text=True, stdout=stdout, stderr=subprocess.PIPE, timeout=300,
        )
        if result.returncode != 0 or result.stderr.strip():
            raise RuntimeError(f"Quint stored-binding replay failed: exit {result.returncode}: {result.stderr.strip()}")
        stdout.seek(0)
        decoded = decode_profile(stdout.read())
    # Emit nothing until the entire actual Quint execution and profile validate.
    for trace in requested:
        print(json.dumps(decoded[trace], separators=(",", ":")))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, RuntimeError, OSError, subprocess.TimeoutExpired) as error:
        print(f"Quint stored-binding replay failed: {error}", file=sys.stderr)
        raise SystemExit(1)
