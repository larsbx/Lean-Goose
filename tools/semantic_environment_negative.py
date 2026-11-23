"""Validate the designated old-record corruption, not a generic failed run.

The expected history is authored from U : Sort 2 := Sort 1, an identity whose
domain is U, and V : Sort 2 := U. No checker or generated witness supplies these
expected semantic fields. The unsafe step changes only U's current stored value
to Sort 0; the two previous snapshots and all predecessor certificates stay
frozen. This is a negative-control contract, not another semantic evaluator.
"""
from __future__ import annotations

from copy import deepcopy
from pathlib import Path

from check_stored_bindings import itf_value
import typing_conversion_profile as profile


def _expected_states() -> list[dict]:
    universe = {"name": [85], "ty": [0, 2], "value": [0, 1], "inferred": [0, 2]}
    identity = {"name": [105, 100], "ty": [5, 2, 1, 85, 2, 1, 85],
                "value": [4, 2, 1, 85, 1, 0], "inferred": [5, 0, 1, 0, 1]}
    alias = {"name": [86], "ty": [0, 2], "value": [2, 1, 85], "inferred": [0, 2]}

    def result(value: list[int]) -> dict:
        return {"value": value, "code": 0}

    universe_certificate = {
        "predecessor": [], "stored": universe, "fuel": 128,
        "declaredSort": result([0, 3]), "valueType": result([0, 2]),
        "normalizedType": result([0, 2]), "inferredNormal": result([0, 2]),
        "declaredNormal": result([0, 2]),
    }
    identity_certificate = {
        "predecessor": [universe], "stored": identity, "fuel": 128,
        "declaredSort": result([0, 2]), "valueType": result([5, 2, 1, 85, 2, 1, 85]),
        "normalizedType": result([5, 0, 1, 0, 1]), "inferredNormal": result([5, 0, 1, 0, 1]),
        "declaredNormal": result([5, 0, 1, 0, 1]),
    }
    alias_certificate = {
        "predecessor": [universe, identity], "stored": alias, "fuel": 128,
        "declaredSort": result([0, 3]), "valueType": result([0, 2]),
        "normalizedType": result([0, 2]), "inferredNormal": result([0, 2]),
        "declaredNormal": result([0, 2]),
    }
    before = {
        "checked": {
            "environment": [universe, identity],
            "snapshots": [{"name": [85], "code": 0, "bindings": [universe]},
                          {"name": [105, 100], "code": 0, "bindings": [universe, identity]}],
            "halted": False, "acceptance_authority": False,
        },
        "certificates": [universe_certificate, identity_certificate],
    }
    wrong_universe = dict(universe, value=[0, 0])
    wrong_environment = [wrong_universe, identity, alias]
    after = deepcopy(before)
    after["checked"]["environment"] = wrong_environment
    after["checked"]["snapshots"].append({"name": [86], "code": 0, "bindings": wrong_environment})
    after["certificates"].append(alias_certificate)
    return [
        {"#meta": {"index": 0}, "s": before, "previous": before,
         "last": {"name": [85], "ty": [0, 2], "value": [0, 1], "fuel": 128}, "hasStep": False},
        {"#meta": {"index": 1}, "s": after, "previous": before,
         "last": {"name": [86], "ty": [0, 2], "value": [2, 1, 85], "fuel": 128}, "hasStep": True},
    ]


def counterexample(exit_code: int, text: str, path: Path) -> None:
    if type(exit_code) is not int or exit_code != 1 or not isinstance(text, str) \
            or "[violation] Found an issue" not in text or "error: Invariant violated" not in text:
        raise ValueError("old-record corruption did not produce the designated invariant failure")
    try:
        witness = itf_value(profile.observations.json_object(path.read_text(encoding="utf-8")))
    except (RecursionError, OverflowError) as error:
        raise ValueError("semantic-environment counterexample is not a bounded JSON witness") from error
    if not isinstance(witness, dict) or set(witness) != {"#meta", "vars", "states"} \
            or not isinstance(witness["#meta"], dict) \
            or not profile.exact(witness["vars"], ["s", "previous", "last", "hasStep"]) \
            or witness["#meta"].get("source") != "SemanticEnvironment.qnt" \
            or witness["#meta"].get("status") != "violation" \
            or witness["#meta"].get("format") != "ITF" \
            or not isinstance(witness["states"], list) or len(witness["states"]) != 2:
        raise ValueError("semantic-environment counterexample has an unexpected source or state inventory")
    if not profile.exact(witness["states"], _expected_states()):
        raise ValueError("counterexample differs from exact old-value corruption with frozen semantic certificates")
