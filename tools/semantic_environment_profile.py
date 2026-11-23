"""Authored compound histories for semantic-environment preservation.

This module supplies syntax and explicit expected full records. It performs no
inference, normalization, conversion, or proof search. The actual Lean/Quint
typing evaluators and pinned native engines execute these histories.
"""
from __future__ import annotations

from typing_conversion_profile import Case, case

CASE_COUNT = 15
INPUT_DEFINITIONS = 75
PROCESSED_SNAPSHOTS = 73
REFERENCE_CASE_COUNT = 12
REFERENCE_OUTCOMES = 62


def cases() -> list[Case]:
    inventory = [
        case("environment_compound_alias_chain", [
            ("U", "s2", "s1", 0, "s2"),
            ("id", "p cU cU", "l cU v0", 0, "p s1 s1"),
            ("alias", "p cU cU", "cid", 0, "p s1 s1"),
            ("aliasAgain", "p cU cU", "calias", 0, "p s1 s1"),
            ("call", "cU", "a caliasAgain s0", 0, "s1"),
            ("use", "s1", "ccall", 0, "s1"),
        ], "Six insertions preserve earlier original fields while inference and conversion follow predecessor aliases."),
        case("environment_declared_type_alias_chain", [
            ("F", "s2", "p s1 s1", 0, "s2"),
            ("G", "s2", "cF", 0, "s2"),
            ("H", "s2", "cG", 0, "s2"),
            ("id", "cH", "l s1 v0", 0, "p s1 s1"),
            ("copy", "cH", "cid", 0, "p s1 s1"),
            ("call", "s1", "a ccopy s0", 0, "s1"),
        ], "Declared type aliases remain original constants while stored inferred fields normalize to Pi."),
        case("environment_forward_reference_recovery", [
            ("early", "s1", "clate", 2, "unknownConstant"),
            ("late", "s1", "s0", 0, "s1"),
            ("early", "s1", "clate", 0, "s1"),
            ("use", "s1", "cearly", 0, "s1"),
        ], "A future declaration cannot justify an earlier refusal; retry succeeds only after its predecessor exists."),
        case("environment_self_reference_refusal", [
            ("seed", "s1", "s0", 0, "s1"),
            ("self", "s1", "cself", 2, "unknownConstant"),
            ("self", "s1", "cseed", 0, "s1"),
        ], "An insertion cannot use itself as a predecessor, and refusal leaves its name available."),
        case("environment_refusals_do_not_bind", [
            ("id", "p s1 s1", "l s1 v0", 0, "p s1 s1"),
            ("blocked", "s1", "s1", 6, "declTypeMismatch"),
            ("missing", "s1", "cblocked", 2, "unknownConstant"),
            ("blocked", "p s1 s1", "cid", 0, "p s1 s1"),
            ("notfn", "s1", "a s0 s0", 5, "funExpected"),
            ("notfn", "s1", "a cblocked s0", 0, "s1"),
            ("use", "s1", "cnotfn", 0, "s1"),
            ("id", "s2", "s1", 3, "alreadyDeclared"),
        ], "Multiple semantic refusals and retries preserve the ordered successful-record history and lookup targets."),
        case("environment_duplicate_full_record", [
            ("id", "p s1 s1", "l s1 v0", 0, "p s1 s1"),
            ("id", "s1", "s0", 3, "alreadyDeclared"),
            ("alias", "p s1 s1", "cid", 0, "p s1 s1"),
            ("id", "p s1 s1", "l s1 s0", 3, "alreadyDeclared"),
            ("call", "s1", "a calias s0", 0, "s1"),
        ], "Duplicate proposals with different types or values cannot replace the record used by later lookup."),
        case("environment_beta_zeta_declared_history", [
            ("beta", "a l s2 v0 s1", "s0", 0, "s1"),
            ("zeta", "t s2 s1 v0", "cbeta", 0, "s1"),
            ("copy", "s1", "czeta", 0, "s1"),
            ("tail", "s1", "ccopy", 0, "s1"),
        ], "Original reducible declarations stay stored while later aliases reuse normalized inferred types."),
        case("environment_dependent_chain", [
            ("dep", "p s1 p v0 v1", "l s1 l v0 v0", 0, "p s1 p v0 v1"),
            ("alias", "p s1 p v0 v1", "cdep", 0, "p s1 p v0 v1"),
            ("atProp", "p s0 s0", "a calias s0", 0, "p s0 s0"),
            ("copy", "p s0 s0", "catProp", 0, "p s0 s0"),
            ("unrelated", "s1", "s0", 0, "s1"),
        ], "A dependent inferred type and its exact stored fields survive aliases, specialization, and unrelated extension."),
        case("environment_erased_future_reference", [
            ("prior", "s1", "s0", 0, "s1"),
            ("erasedBeta", "s1", "a l s1 s0 clater", 2, "unknownConstant"),
            ("erasedLet", "s1", "t s1 clater s0", 2, "unknownConstant"),
            ("later", "s1", "cprior", 0, "s1"),
            ("erasedBeta", "s1", "a l s1 s0 clater", 0, "s1"),
            ("erasedLet", "s1", "t s1 clater s0", 0, "s1"),
            ("after", "s1", "cerasedLet", 0, "s1"),
        ], "Original syntax must use already available constants even when beta or zeta would erase them."),
        case("environment_failed_annotation_retry", [
            ("seed", "s1", "s0", 0, "s1"),
            ("retry", "t s2 s0 s1", "cseed", 6, "letTypeMismatch"),
            ("retry", "t s2 s1 v0", "cseed", 0, "s1"),
            ("use", "s1", "cretry", 0, "s1"),
        ], "Malformed type annotations leave no binding; corrected retry preserves the prior semantic history."),
        case("environment_scope_after_history", [
            ("U", "s2", "s1", 0, "s2"),
            ("id", "p cU cU", "l cU v0", 0, "p s1 s1"),
            ("alias", "p cU cU", "cid", 0, "p s1 s1"),
            ("stop", "s1", "v0", 1, "Invalid_scope"),
            ("unprocessed", "s1", "s0", 0, "s1"),
        ], "Fatal scope preserves three semantic bindings and prevents every later insertion.", references=False),
        case("environment_duplicate_priority_after_history", [
            ("U", "s2", "s1", 0, "s2"),
            ("id", "p cU cU", "l cU v0", 0, "p s1 s1"),
            ("id", "v0", "cmissing", 3, "alreadyDeclared"),
            ("call", "s1", "a cid s0", 0, "s1"),
            ("use", "s1", "ccall", 0, "s1"),
        ], "Duplicate priority preserves a compound predecessor despite invalid replacement syntax.", references=False),
        case("environment_deep_dependent_context", [
            ("P", "s1", "s0", 0, "s1"),
            ("first", "p s1 p s1 p v1 v2", "l s1 l s1 l v1 v0", 0, "p s1 p s1 p v1 v2"),
            ("specialize", "p s1 p cP cP", "a cfirst cP", 0, "p s1 p s0 s0"),
            ("atProp", "p cP cP", "a cspecialize s0", 0, "p s0 s0"),
        ], "Lifting under three binders and specialization through delta preserve all original and normalized fields."),
        case("environment_normalized_field_conversion_retry", [
            ("U", "s2", "s1", 0, "s2"),
            ("id", "t s2 cU p v0 v1", "l cU v0", 0, "p s1 s1"),
            ("bad", "p s1 s2", "cid", 6, "declTypeMismatch"),
            ("missing", "p s1 s1", "cbad", 2, "unknownConstant"),
            ("bad", "p cU cU", "cid", 0, "p s1 s1"),
            ("call", "s1", "a cbad s0", 0, "s1"),
        ], "A refused conversion cannot bind its name or replace an existing normalized inferred field."),
        case("environment_dependent_annotation_outside_outer_context", [
            ("dep", "p s1 p v0 v1", "l s1 l v0 v0", 0, "p s1 p v0 v1"),
            ("stop", "p s1 p v1 v1", "l s1 l v0 v0", 1, "Invalid_scope"),
            ("unprocessed", "s1", "s0", 0, "s1"),
        ], "An inner domain cannot borrow its own binder; fatal scope retains the dependent binding and stops insertion.",
            references=False),
    ]
    common = [item for item in inventory if item.lean_outcomes is not None]
    if len(inventory) != CASE_COUNT or len({item.name for item in inventory}) != CASE_COUNT \
            or sum(len(item.request["definitions"]) for item in inventory) != INPUT_DEFINITIONS \
            or sum(len(item.expected["steps"]) for item in inventory) != PROCESSED_SNAPSHOTS \
            or len(common) != REFERENCE_CASE_COUNT \
            or sum(len(item.expected["steps"]) for item in common) != REFERENCE_OUTCOMES:
        raise ValueError("semantic-environment history inventory changed")
    return inventory
