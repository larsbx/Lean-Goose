#!/usr/bin/env python3
"""Evaluate the declared bounded trace profile with the real pinned Quint CLI.

Input: one nonempty kind,name,target;... trace per line, of length at most three
and drawn from the model's ten actions over names 0 and 1. Output: one JSON model
observation per input line. Quint enumerates and evaluates all 1,110 profile
traces in one expression. This adapter checks trace identities and translates
numeric wire values; it implements no transaction semantics.
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

HERE = Path(__file__).resolve().parent
ACTIONS = (
    (0, 0, 0), (0, 1, 0), (1, 0, 0), (1, 1, 0),
    (2, 0, 0), (2, 0, 1), (2, 1, 0), (2, 1, 1),
    (3, 0, 0), (3, 1, 0),
)
PROFILE = {trace for length in (1, 2, 3) for trace in itertools.product(ACTIONS, repeat=length)}


def trace_key(line: str) -> tuple[tuple[int, ...], ...]:
    if not re.fullmatch(r"[0-3],[01],[01](?:;[0-3],[01],[01]){0,2}", line):
        raise ValueError("trace is outside the three-step, two-name profile")
    trace = tuple(tuple(int(value) for value in item.split(",")) for item in line.split(";"))
    if trace not in PROFILE:
        raise ValueError("trace contains an action outside the declared ten-action profile")
    return trace


def observation(value: object) -> dict:
    if not isinstance(value, list) or len(value) < 4 or any(type(item) is not int or item < 0 for item in value):
        raise ValueError("Quint replay returned an invalid numeric wire vector")
    halted, authority, count = value[:3]
    if halted not in (0, 1) or authority not in (0, 1) or len(value) < count + 4:
        raise ValueError("Quint replay returned invalid flags or environment length")
    environment = value[3:3 + count]
    outcome_count = value[3 + count]
    pairs = value[4 + count:]
    if len(pairs) != 2 * outcome_count:
        raise ValueError("Quint replay returned an inconsistent outcome length")
    return {
        "halted": bool(halted),
        "outcomes": [{"name": pairs[i], "code": pairs[i + 1]} for i in range(0, len(pairs), 2)],
        "environment": environment,
        "successes": count,
        "acceptance_authority": bool(authority),
    }


def decode_profile(text: str) -> dict:
    values = json.loads(text)
    if not isinstance(values, list) or len(values) != len(PROFILE):
        raise ValueError("Quint did not return the complete 1,110-case profile")
    decoded = {}
    for value in values:
        if not isinstance(value, list) or not value or type(value[0]) is not int or value[0] not in (1, 2, 3):
            raise ValueError("Quint replay returned invalid trace framing")
        length = value[0]
        if len(value) < 1 + 3 * length:
            raise ValueError("Quint replay returned a truncated trace identity")
        fields = value[1:1 + 3 * length]
        if any(type(item) is not int for item in fields):
            raise ValueError("Quint replay returned a nonintegral trace identity")
        trace = tuple(tuple(fields[i:i + 3]) for i in range(0, len(fields), 3))
        if trace not in PROFILE or trace in decoded:
            raise ValueError("Quint replay returned an unknown or duplicate trace identity")
        decoded[trace] = observation(value[1 + 3 * length:])
    if set(decoded) != PROFILE:
        raise ValueError("Quint replay omitted a required trace")
    return decoded


def main() -> int:
    lines = sys.stdin.read().splitlines()
    if not lines or any(not line for line in lines):
        raise ValueError("at least one nonempty trace is required")
    requested = [trace_key(line) for line in lines]
    name = os.environ.get("QUINT", str(HERE / "node_modules/.bin/quint"))
    quint = shutil.which(name)
    if quint is None:
        raise ValueError("missing Quint executable")
    result = subprocess.run(
        [quint, "repl", "--require", str(HERE / "DefinitionTransactions.qnt") + "::DefinitionTransactions",
         "--backend=typescript", "--quiet"],
        input="replayProfile\n", text=True, capture_output=True, timeout=300,
    )
    if result.returncode != 0 or result.stderr.strip():
        raise RuntimeError(f"Quint replay failed: exit {result.returncode}: {result.stderr.strip()}")
    decoded = decode_profile(result.stdout)
    # Emit nothing unless the complete Quint profile and framing were valid.
    for trace in requested:
        print(json.dumps(decoded[trace], separators=(",", ":")))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, RuntimeError, OSError, subprocess.TimeoutExpired) as error:
        print(f"Quint replay failed: {error}", file=sys.stderr)
        raise SystemExit(1)
