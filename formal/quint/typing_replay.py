#!/usr/bin/env python3
"""Execute the actual Quint typing/conversion model on strict source-bound JSONL.

Python validates request and result framing only. All scope, inference,
normalization, conversion, and stored-field computations run in Quint.
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

from substitution_replay import ascii_name, invalid_constant, natural, object_pairs, vector_literal

HERE = Path(__file__).resolve().parent
BATCH_SIZE = 4
SCHEMA = "lean-goose.typing-conversion-model.v1"


def request(line: str) -> dict[str, Any]:
    value = json.loads(line, object_pairs_hook=object_pairs, parse_constant=invalid_constant)
    if not isinstance(value, dict) or set(value) != {"nodes", "definitions", "fuel"} \
            or not isinstance(value["nodes"], list) or not 1 <= len(value["nodes"]) <= 128 \
            or not isinstance(value["definitions"], list) or not 1 <= len(value["definitions"]) <= 64 \
            or not natural(value["fuel"]) or value["fuel"] > 256:
        raise ValueError("expected exactly 1..128 nodes, 1..64 definitions, and natural fuel at most 256")
    expanded_lengths: list[int] = []
    expanded_total = 0
    for index, raw in enumerate(value["nodes"]):
        if not isinstance(raw, list) or len(raw) != 5 or any(not natural(n) for n in raw[:4]):
            raise ValueError("raw nodes require five fields and four natural-number scalars")
        tag, a, b, c, name = raw
        if tag not in range(7) or not isinstance(name, list):
            raise ValueError("unknown node tag or malformed name-code list")
        if tag == 2:
            if (a, b, c) != (0, 0, 0) or not ascii_name(name):
                raise ValueError("constant nodes require canonical zero fields and an ASCII identifier")
        elif name or (tag in (0, 1) and (b != 0 or c != 0)) or (tag in (3, 4, 5) and c != 0):
            raise ValueError("unused raw fields must be canonical zeros or an empty name")
        children = [a, b, c] if tag == 6 else [a, b] if tag in (3, 4, 5) else []
        if any(child >= index for child in children):
            raise ValueError("every child must refer to an earlier node")
        length = (2 + len(name) if tag == 2 else 2) if tag < 3 \
            else 1 + sum(expanded_lengths[child] for child in children)
        expanded_lengths.append(length)
        expanded_total += length
        if expanded_total > 65536:
            raise ValueError("aggregate expanded expression wires exceed 65536 tokens")
    for definition in value["definitions"]:
        if not isinstance(definition, list) or len(definition) != 3 or not ascii_name(definition[0]) \
                or any(not natural(index) or index >= len(value["nodes"]) for index in definition[1:]):
            raise ValueError("definitions require an ASCII name and two in-range natural node IDs")
    return value


def request_literal(index: int, value: dict[str, Any]) -> str:
    nodes = ",".join("D::node(" + ",".join(str(number) for number in raw[:4]) + ","
                     + vector_literal(raw[4]) + ")" for raw in value["nodes"])
    definitions = ",".join(f"definition({vector_literal(name)},{ty},{term})"
                           for name, ty, term in value["definitions"])
    return f"replayRequest({index},List({nodes}),List({definitions}),{value['fuel']})"


def identity(index: int, value: dict[str, Any]) -> list[int]:
    result = [index, len(value["nodes"])]
    for raw in value["nodes"]:
        result.extend(raw[:4])
        result.append(len(raw[4]))
        result.extend(raw[4])
    result.append(len(value["definitions"]))
    for name, ty, term in value["definitions"]:
        result.append(len(name))
        result.extend(name)
        result.extend((ty, term))
    result.append(value["fuel"])
    return result


class Wire:
    def __init__(self, values: Any):
        if not isinstance(values, list) or any(not natural(value) for value in values):
            raise ValueError("Quint returned a nonintegral or negative wire field")
        self.values = values
        self.position = 0

    def number(self) -> int:
        if self.position >= len(self.values):
            raise ValueError("Quint returned truncated result framing")
        value = self.values[self.position]
        self.position += 1
        return value

    def vector(self) -> list[int]:
        size = self.number()
        if size > len(self.values) - self.position:
            raise ValueError("Quint returned a truncated vector")
        result = self.values[self.position:self.position + size]
        self.position += size
        return result

    def observation(self, index: int, value: dict[str, Any]) -> dict[str, Any]:
        expected_identity = identity(index, value)
        if self.values[:len(expected_identity)] != expected_identity:
            raise ValueError("Quint returned a changed, missing, duplicated, or reordered request identity")
        self.position = len(expected_identity)
        halted, authority, count = self.number(), self.number(), self.number()
        if halted not in (0, 1) or authority != 0 or not 1 <= count <= len(value["definitions"]):
            raise ValueError("Quint returned invalid halt, authority, or snapshot framing")
        steps = []
        for position in range(count):
            name, code, binding_count = self.vector(), self.number(), self.number()
            if name != value["definitions"][position][0]:
                raise ValueError("Quint returned reordered snapshot identities")
            if code == 10:
                raise ValueError("Quint continuation machine exceeded its 2048-transition cap")
            if code not in (0, 1, 2, 3, 4, 5, 6, 9) or binding_count > position + 1:
                raise ValueError("Quint returned an unsupported outcome or binding framing")
            bindings = []
            for _ in range(binding_count):
                binding = dict(zip(("name", "type", "value", "inferred"), (self.vector() for _ in range(4))))
                if not ascii_name(binding["name"]) or any(not binding[key] for key in ("type", "value", "inferred")):
                    raise ValueError("Quint returned malformed stored fields")
                bindings.append(binding)
            steps.append({"name": name, "outcome": code, "bindings": bindings})
        if self.position != len(self.values):
            raise ValueError("Quint returned trailing result fields")
        if any(row["outcome"] in (1, 9) for row in steps[:-1]) \
                or bool(halted) != (steps[-1]["outcome"] in (1, 9)) \
                or (not halted and count != len(value["definitions"])):
            raise ValueError("Quint returned inconsistent terminal framing")
        return {"schema": SCHEMA, "steps": steps, "halted": bool(halted), "acceptance_authority": False}


def decode_batches(text: str, requested: list[dict[str, Any]]) -> list[dict[str, Any]]:
    decoder = json.JSONDecoder(parse_constant=invalid_constant)
    position = 0
    observations = []
    for start in range(0, len(requested), BATCH_SIZE):
        batch = requested[start:start + BATCH_SIZE]
        while position < len(text) and text[position].isspace():
            position += 1
        if position == len(text):
            raise ValueError("Quint returned a missing replay batch")
        values, position = decoder.raw_decode(text, position)
        if not isinstance(values, list) or len(values) != len(batch):
            raise ValueError("Quint returned an incorrect replay-batch cardinality")
        for offset, (wire, value) in enumerate(zip(values, batch)):
            observations.append(Wire(wire).observation(start + offset, value))
    if text[position:].strip():
        raise ValueError("Quint returned an extra batch or trailing output")
    return observations


def main() -> int:
    lines = sys.stdin.read().splitlines()
    if not lines or any(not line.strip() for line in lines):
        raise ValueError("at least one nonempty typing/conversion JSON line is required")
    requested = [request(line) for line in lines]
    literals = [request_literal(index, value) for index, value in enumerate(requested)]
    commands = "\n".join("List(" + ",".join(literals[start:start + BATCH_SIZE]) + ")"
                         for start in range(0, len(literals), BATCH_SIZE)) + "\n"
    name = os.environ.get("QUINT", str(HERE / "node_modules/.bin/quint"))
    quint = shutil.which(name)
    if quint is None:
        raise ValueError("missing Quint executable")
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8") as stdout:
        result = subprocess.run(
            [quint, "repl", "--require", str(HERE / "TypingConversion.qnt") + "::TypingConversion",
             "--backend=typescript", "--quiet"], input=commands, text=True,
            stdout=stdout, stderr=subprocess.PIPE, timeout=300,
        )
        if result.returncode or result.stderr.strip():
            raise RuntimeError(f"actual Quint evaluation failed: exit {result.returncode}: {result.stderr.strip()}")
        stdout.seek(0)
        decoded = decode_batches(stdout.read(), requested)
    for result in decoded:
        print(json.dumps(result, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, RuntimeError, OSError, subprocess.TimeoutExpired) as error:
        print(f"Quint typing replay failed: {error}", file=sys.stderr)
        raise SystemExit(1)
