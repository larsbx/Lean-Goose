#!/usr/bin/env python3
"""Evaluate lift/substitution with the pinned Quint TypeScript evaluator.

Input is JSONL with exactly nodes, operation, root, parameter, cutoff, depths.
Operation 0 lifts by parameter; operation 1 substitutes the node at parameter.
Python validates only canonical input and length-framed evaluator output.
Every expression operation, topology decision, and metadata result is Quint's.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from typing import Any

HERE = Path(__file__).resolve().parent
BATCH_SIZE = 32


def object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON object key")
        result[key] = value
    return result


def invalid_constant(value: str) -> None:
    raise ValueError(f"nonfinite JSON constant: {value}")


def natural(value: Any) -> bool:
    return type(value) is int and value >= 0


def ascii_name(value: Any) -> bool:
    return isinstance(value, list) and bool(value) and all(
        type(code) is int and (48 <= code <= 57 or 65 <= code <= 90 or 97 <= code <= 122 or code == 95)
        for code in value
    )


def request(line: str) -> dict[str, Any]:
    value = json.loads(line, object_pairs_hook=object_pairs, parse_constant=invalid_constant)
    if not isinstance(value, dict) or set(value) != {"nodes", "operation", "root", "parameter", "cutoff", "depths"} \
            or not isinstance(value["nodes"], list) or not value["nodes"] \
            or not isinstance(value["depths"], list) \
            or any(not natural(depth) for depth in value["depths"]) \
            or any(not natural(value[field]) for field in ("operation", "root", "parameter", "cutoff")):
        raise ValueError("expected exactly nonempty nodes, natural operation arguments, and natural-number depths")
    if value["operation"] not in (0, 1) or value["root"] >= len(value["nodes"]) \
            or (value["operation"] == 1 and value["parameter"] >= len(value["nodes"])):
        raise ValueError("unknown operation or out-of-range root/replacement ID")
    for raw in value["nodes"]:
        if not isinstance(raw, list) or len(raw) != 5 or any(not natural(n) for n in raw[:4]):
            raise ValueError("each raw node must have five fields with four natural-number scalars")
        tag, a, b, c, name = raw
        if tag not in range(7) or not isinstance(name, list):
            raise ValueError("unknown node tag or malformed name-code list")
        if tag == 2:
            if (a, b, c) != (0, 0, 0) or not ascii_name(name):
                raise ValueError("a constant requires zero numeric fields and a nonempty ASCII identifier")
        elif name or (tag in (0, 1) and (b != 0 or c != 0)) or (tag in (3, 4, 5) and c != 0):
            raise ValueError("unused raw node fields must be canonical zeros or an empty name list")
    return value


def vector_literal(values: list[int]) -> str:
    return "List(" + ",".join(str(value) for value in values) + ")"


def request_literal(index: int, value: dict[str, Any]) -> str:
    nodes = ",".join(
        "node(" + ",".join(str(number) for number in raw[:4]) + "," + vector_literal(raw[4]) + ")"
        for raw in value["nodes"]
    )
    arguments = ",".join(str(value[field]) for field in ("operation", "root", "parameter", "cutoff"))
    return f"replayRequest({index},List({nodes}),{arguments},{vector_literal(value['depths'])})"


def identity(index: int, value: dict[str, Any]) -> list[int]:
    result = [index, len(value["nodes"])]
    for raw in value["nodes"]:
        result.extend(raw[:4])
        result.append(len(raw[4]))
        result.extend(raw[4])
    result.extend(value[field] for field in ("operation", "root", "parameter", "cutoff"))
    result.append(len(value["depths"]))
    result.extend(value["depths"])
    return result


class Wire:
    """Read exact numeric framing, without interpreting expression semantics."""

    def __init__(self, values: Any):
        if not isinstance(values, list) or any(not natural(value) for value in values):
            raise ValueError("Quint returned a nonintegral or negative wire field")
        self.values = values
        self.position = 0

    def number(self) -> int:
        if self.position >= len(self.values):
            raise ValueError("Quint returned a truncated substitution result")
        value = self.values[self.position]
        self.position += 1
        return value

    def vector(self) -> list[int]:
        size = self.number()
        if size > len(self.values) - self.position:
            raise ValueError("Quint returned a truncated length-framed vector")
        result = self.values[self.position:self.position + size]
        self.position += size
        return result

    def observation(self, index: int, value: dict[str, Any]) -> dict[str, Any]:
        expected = identity(index, value)
        if self.values[:len(expected)] != expected:
            raise ValueError("Quint returned a changed, missing, duplicated or reordered request identity")
        self.position = len(expected)
        decoded, authority, count = self.number(), self.number(), self.number()
        if decoded not in (0, 1) or authority != 0:
            raise ValueError("Quint returned invalid decode or authority flags")
        if count != (1 if decoded else 0):
            raise ValueError("Quint returned a partial or additional transformed-root inventory")
        expressions, heights, loose, scoped = [], [], [], []
        for _ in range(count):
            expressions.append(self.vector())
            heights.append(self.number())
            loose.append(self.number())
            bits = self.vector()
            if len(bits) != len(value["depths"]) or any(bit not in (0, 1) for bit in bits):
                raise ValueError("Quint returned an invalid scope-query inventory")
            scoped.append([bool(bit) for bit in bits])
        if self.position != len(self.values):
            raise ValueError("Quint returned trailing substitution wire data")
        return {"decoded": bool(decoded), "expressions": expressions, "heights": heights,
                "loose": loose, "scoped": scoped, "acceptance_authority": False}


def decode_batches(text: str, requested: list[dict[str, Any]]) -> list[dict[str, Any]]:
    batches = [requested[start:start + BATCH_SIZE] for start in range(0, len(requested), BATCH_SIZE)]
    decoder = json.JSONDecoder(parse_constant=invalid_constant)
    position = 0
    observations = []
    for batch_index, batch in enumerate(batches):
        while position < len(text) and text[position].isspace():
            position += 1
        if position == len(text):
            raise ValueError("Quint returned a missing replay batch")
        values, position = decoder.raw_decode(text, position)
        if not isinstance(values, list) or len(values) != len(batch):
            raise ValueError("Quint returned a missing or additional replay case")
        for offset, (wire, value) in enumerate(zip(values, batch)):
            observations.append(Wire(wire).observation(batch_index * BATCH_SIZE + offset, value))
    if text[position:].strip():
        raise ValueError("Quint returned an additional replay batch or trailing output")
    return observations


def main() -> int:
    lines = sys.stdin.read().splitlines()
    if not lines or any(not line.strip() for line in lines):
        raise ValueError("at least one nonempty substitution JSON line is required")
    requested = [request(line) for line in lines]
    literals = [request_literal(index, value) for index, value in enumerate(requested)]
    commands = "\n".join("List(" + ",".join(literals[start:start + BATCH_SIZE]) + ")"
                         for start in range(0, len(literals), BATCH_SIZE)) + "\n"
    name = os.environ.get("QUINT", str(HERE / "node_modules/.bin/quint"))
    quint = shutil.which(name)
    if quint is None:
        raise ValueError("missing Quint executable")
    # Actual Quint evaluates all commands. A regular file prevents large
    # pretty-printed responses from being truncated by pipe-buffer shutdown.
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8") as stdout:
        result = subprocess.run(
            [quint, "repl", "--require", str(HERE / "Substitution.qnt") + "::Substitution",
             "--backend=typescript", "--quiet"],
            input=commands, text=True, stdout=stdout, stderr=subprocess.PIPE, timeout=300,
        )
        if result.returncode != 0 or result.stderr.strip():
            raise RuntimeError(f"Quint substitution replay failed: exit {result.returncode}: {result.stderr.strip()}")
        stdout.seek(0)
        decoded = decode_batches(stdout.read(), requested)
    # Validate every echoed identity, including across batches, before any
    # observation is emitted. Evaluator errors never become topology refusals.
    for result in decoded:
        print(json.dumps(result, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, RuntimeError, OSError, subprocess.TimeoutExpired) as error:
        print(f"Quint substitution replay failed: {error}", file=sys.stderr)
        raise SystemExit(1)
