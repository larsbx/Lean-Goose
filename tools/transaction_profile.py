"""Finite inputs and observable projections for the definition-transaction models.

The semantic predictions come from the executed Lean and Quint models. This
module constructs native inputs and checks the output contract; it does not
implement a third transaction semantics.
"""
from __future__ import annotations

from itertools import product
from typing import Any

import run as observations

Action = tuple[int, int, int]
ACTIONS: tuple[Action, ...] = (
    (0, 0, 0), (0, 1, 0), (1, 0, 0), (1, 1, 0),
    (2, 0, 0), (2, 0, 1), (2, 1, 0), (2, 1, 1),
    (3, 0, 0), (3, 1, 0),
)
OUTCOMES = {0: "observed_success", 2: "Unknown_constant",
            3: "Duplicate_definition", 6: "Type_mismatch"}
CASE_COUNT = 1110


def cases() -> list[tuple[Action, ...]]:
    return [word for length in range(1, 4) for word in product(ACTIONS, repeat=length)]


def encode(actions: tuple[Action, ...]) -> str:
    if not 1 <= len(actions) <= 3 or any(action not in ACTIONS for action in actions):
        raise ValueError("trace is outside the declared finite action profile")
    return ";".join(",".join(str(value) for value in action) for action in actions)


def fixture(actions: tuple[Action, ...]) -> str:
    encode(actions)
    # Sort0 : Sort1 is the good definition. Sort1 : Sort1 is ill-typed.
    # Var0 triggers the designated scope failure only when the name is fresh.
    # Constant nodes are imported but looked up only when their definition runs.
    rows = ["lean-ocaml-benchmark-dag-v1", "n\t0\ts\t0", "n\t1\ts\t1",
            "n\t2\tv\t0", "n\t3\tc\tformal0", "n\t4\tc\tformal1"]
    for kind, name, target in actions:
        value = {0: 0, 1: 1, 2: 3 + target, 3: 2}[kind]
        rows.append(f"d\tformal{name}\t1\t{value}")
    return "\n".join(rows) + "\n"


def validate_model(row: dict[str, Any], actions: tuple[Action, ...]) -> None:
    fields = {"halted", "outcomes", "environment", "successes", "acceptance_authority"}
    if not isinstance(row, dict) or set(row) != fields or type(row["halted"]) is not bool \
            or row["acceptance_authority"] is not False:
        raise ValueError("unknown model result or non-observational authority")
    env, outcomes = row["environment"], row["outcomes"]
    if not isinstance(env, list) or any(type(n) is not int or n not in (0, 1) for n in env) \
            or len(env) != len(set(env)):
        raise ValueError("malformed model environment projection")
    if not isinstance(outcomes, list) or len(outcomes) > len(actions):
        raise ValueError("malformed model observation inventory")
    for index, outcome in enumerate(outcomes):
        if not isinstance(outcome, dict) or set(outcome) != {"name", "code"} \
                or type(outcome["name"]) is not int or outcome["name"] != actions[index][1] \
                or type(outcome["code"]) is not int or outcome["code"] not in OUTCOMES:
            raise ValueError("malformed or reordered model observation")
    if type(row["successes"]) is not int or row["successes"] != len(env) \
            or row["successes"] != sum(x["code"] == 0 for x in outcomes):
        raise ValueError("model success count differs from its ledger")
    if env != [row["name"] for row in outcomes if row["code"] == 0]:
        raise ValueError("model environment differs from its ordered successful names")
    if (not row["halted"] and len(outcomes) != len(actions)) \
            or (row["halted"] and len(outcomes) >= len(actions)):
        raise ValueError("model completion inventory is inconsistent")


def decode_models(text: str, inventory: list[tuple[Action, ...]]) -> list[dict[str, Any]]:
    lines = text.splitlines()
    if len(lines) != len(inventory):
        raise ValueError("model replay returned a missing or additional result")
    result = []
    for line, actions in zip(lines, inventory):
        row = observations.json_object(line)
        validate_model(row, actions)
        result.append(row)
    return result


def check_native(expected: dict[str, Any], exit_code: int, stdout: str,
                 stderr: str) -> dict[str, Any]:
    if expected["halted"]:
        if exit_code != 2 or stdout.strip() \
                or stderr.strip() != "goose bounded checker: Invalid_scope":
            raise ValueError("native scope failure did not match the designated fatal outcome")
        return {"halted": True, "exit_code": exit_code, "diagnostic": stderr.strip(),
                "completed_receipt": False}
    if exit_code != 0 or stderr:
        raise ValueError("native execution failed instead of completing its observation receipt")
    projected = [{"name": f"formal{row['name']}", "outcome": OUTCOMES[row["code"]]}
                 for row in expected["outcomes"]]
    observed = observations.definition_observation("goose-aot", observations.json_object(stdout), projected)
    if observed["success_observations"] != expected["successes"]:
        raise ValueError("native success count differs from the model projection")
    return observed
