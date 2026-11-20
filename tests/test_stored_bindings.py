"""Boundary controls for complete stored records, trace framing, and derivation."""
from copy import deepcopy
import difflib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import check_stored_bindings as stored_gate
import runtime
import source_derivation as derivation
import stored_binding_profile as profile

spec = importlib.util.spec_from_file_location("stored_quint_wire", ROOT / "formal/quint/stored_replay.py")
quint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(quint)


def nodes():
    return [{"tag": "s", "a": level, "b": 0, "c": 0, "name": ""} for level in range(3)] + [
        {"tag": "v", "a": 0, "b": 0, "c": 0, "name": ""},
        {"tag": "c", "a": 0, "b": 0, "c": 0, "name": "formal0"},
        {"tag": "c", "a": 0, "b": 0, "c": 0, "name": "formal1"},
    ]


def example(kind="refusal"):
    """Three authored examples; no replacement definition evaluator."""
    first = {"name": 0, "type": [0, 1], "value": [0, 0], "inferred": [0, 1]}
    raw_first = {"name": "formal0", "type": 1, "value": 0, "inferred": 1}
    first_snapshot = {"name": 0, "code": 0, "environment": [first]}
    if kind == "refusal":
        actions = ((0, 0, 0, 0), (1, 1, 0, 0))
        second_snapshot = {"name": 1, "code": 6, "environment": [first]}
        raw_final = [raw_first]
    elif kind == "alias":
        actions = ((0, 0, 0, 0), (2, 1, 0, 0))
        second = {"name": 1, "type": [0, 1], "value": [2, 0], "inferred": [0, 1]}
        second_snapshot = {"name": 1, "code": 0, "environment": [first, second]}
        raw_final = [raw_first, {"name": "formal1", "type": 1, "value": 4, "inferred": 1}]
    elif kind == "fatal":
        actions = ((0, 0, 0, 0), (3, 1, 0, 0), (0, 1, 0, 0))
        second_snapshot = {"name": 1, "code": 1, "environment": [first]}
        raw_final = [raw_first]
    else:
        raise AssertionError("unknown authored example")
    snapshots = [deepcopy(first_snapshot), deepcopy(second_snapshot)]
    expected = {"halted": kind == "fatal", "environment": deepcopy(second_snapshot["environment"]),
                "outcomes": [{"name": s["name"], "code": s["code"]} for s in snapshots if s["code"] != 1],
                "successes": len(raw_final), "acceptance_authority": False, "snapshots": snapshots}
    raw = {"schema": profile.TRACE_SCHEMA, "engine": "goose-aot",
           "status": "halted" if kind == "fatal" else "traced", "success_observations": len(raw_final),
           "acceptance_authority": False, "steps": [
               {"name": "formal0", "outcome": "observed_success", "bindings": deepcopy([raw_first]), "nodes": nodes()},
               {"name": "formal1", "outcome": profile.OUTCOMES[second_snapshot["code"]],
                "bindings": deepcopy(raw_final), "nodes": nodes()},
           ]}
    return actions, expected, raw


def check(expected, actions, raw, exit_code=0, stderr=""):
    return profile.check_trace(expected, actions, exit_code, json.dumps(raw) + "\n", stderr)


class StoredProfileControls(unittest.TestCase):
    def test_complete_two_level_inventory_and_fixture(self):
        cases = profile.cases()
        self.assertEqual(len(set(cases)), 2954)
        self.assertEqual([sum(len(c) == n for c in cases) for n in (1, 2, 3)], [14, 196, 2744])
        self.assertEqual(profile.ACTIONS, quint.ACTIONS)
        self.assertIn(((0, 0, 0, 1), (2, 1, 0, 0), (2, 1, 0, 1)), cases)
        self.assertIn(((0, 1, 0, 0), (2, 0, 1, 1)), cases)
        fixture = profile.fixture(((0, 0, 0, 1), (2, 1, 0, 1)))
        self.assertIn("n\t2\ts\t2\n", fixture)
        self.assertTrue(fixture.endswith("d\tformal0\t2\t1\nd\tformal1\t2\t4\n"))

    def test_profile_rejects_out_of_scope_and_noninteger_actions(self):
        invalid = [(), ((0, 0, 0, 0),) * 4, ((0, 0, 0, 2),), ((2, 0, 0, 1),),
                   ((4, 0, 0, 0),), ((0, 2, 0, 0),), ((0, 0, 1, 0),),
                   ((False, 0, 0, 0),), ((0, False, 0, 0),), ((0, 0, False, 0),),
                   ((0, 0, 0, False),), ((0.0, 0, 0, 0),), ((0, 0, 0),)]
        for actions in invalid:
            with self.subTest(actions=actions), self.assertRaises(ValueError):
                profile.fixture(actions)

    def test_authored_success_refusal_alias_and_fatal_examples(self):
        for kind in ("refusal", "alias", "fatal"):
            actions, expected, raw = example(kind)
            profile.validate_model(expected, actions)
            self.assertEqual(check(expected, actions, raw, 2 if kind == "fatal" else 0,
                                   "goose bounded checker: Invalid_scope\n" if kind == "fatal" else ""), raw)

    def test_model_refusal_preserves_each_existing_payload(self):
        for field in ("type", "value", "inferred"):
            actions, expected, _ = example()
            expected["snapshots"][1]["environment"][0][field] = [0, 2]
            expected["environment"][0][field] = [0, 2]
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "refusal or fatal failure changed"):
                profile.validate_model(expected, actions)

    def test_model_success_preserves_previous_complete_records(self):
        actions, expected, _ = example("alias")
        expected["snapshots"][1]["environment"][0]["inferred"] = [0, 2]
        expected["environment"][0]["inferred"] = [0, 2]
        with self.assertRaisesRegex(ValueError, "success did not append"):
            profile.validate_model(expected, actions)

    def test_model_rejects_snapshot_loss_reorder_and_posthalt_steps(self):
        mutations = [lambda r: r.update(snapshots=[]), lambda r: r["snapshots"].pop(),
                     lambda r: r.update(snapshots=list(reversed(r["snapshots"]))),
                     lambda r: r["snapshots"][1].update(name=0),
                     lambda r: r["snapshots"][1].update(code=1),
                     lambda r: r.update(halted=True)]
        for mutate in mutations:
            actions, expected, _ = example()
            mutate(expected)
            with self.subTest(mutation=mutate), self.assertRaises(ValueError):
                profile.validate_model(expected, actions)
        actions, expected, _ = example("fatal")
        expected["snapshots"].append(deepcopy(expected["snapshots"][-1]))
        with self.assertRaises(ValueError):
            profile.validate_model(expected, actions)

    def test_model_rejects_boolean_numeric_fields_and_extra_keys(self):
        mutations = [lambda r: r.update(successes=True), lambda r: r.update(acceptance_authority=0),
                     lambda r: r.update(halted=0), lambda r: r.update(extra=0),
                     lambda r: r["snapshots"][0].update(name=False),
                     lambda r: r["snapshots"][0].update(code=False),
                     lambda r: r["environment"][0].update(name=False),
                     lambda r: r["environment"][0]["type"].__setitem__(0, False),
                     lambda r: r["outcomes"][0].update(name=False),
                     lambda r: r["outcomes"][0].update(code=False),
                     lambda r: r["snapshots"][0].update(extra="ignored")]
        for mutate in mutations:
            actions, expected, _ = example()
            mutate(expected)
            with self.subTest(mutation=mutate), self.assertRaises(ValueError):
                profile.validate_model(expected, actions)

    def test_model_json_requires_exact_inventory_and_unique_fields(self):
        actions, expected, _ = example()
        text = json.dumps(expected) + "\n"
        self.assertEqual(profile.decode_models(text, [actions]), [expected])
        for bad in ("", text * 2, text.replace('"halted": false', '"halted": false, "halted": false'),
                    text.replace('"code": 6', '"code": NaN')):
            with self.subTest(text=bad), self.assertRaises(ValueError):
                profile.decode_models(bad, [actions])

    def test_native_refusal_rejects_mutated_payload_fields(self):
        for field, node_id in (("type", 2), ("value", 1), ("inferred", 2)):
            actions, expected, raw = example()
            raw["steps"][1]["bindings"][0][field] = node_id
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "payload differs"):
                check(expected, actions, raw)

    def test_raw_identity_changes_refused_even_when_payload_is_equal(self):
        for kind in ("refusal", "alias"):
            for field in ("type", "value", "inferred"):
                actions, expected, raw = example(kind)
                second = raw["steps"][1]
                same = deepcopy(second["nodes"][second["bindings"][0][field]])
                second["nodes"].append(same)
                second["bindings"][0][field] = len(second["nodes"]) - 1
                with self.subTest(kind=kind, field=field), self.assertRaisesRegex(ValueError, "raw stored binding|old IDs"):
                    check(expected, actions, raw)

    def test_alias_keeps_constant_value_and_original_declared_type_id(self):
        actions, expected, raw = example("alias")
        raw["steps"][1]["bindings"][1]["value"] = 0
        with self.assertRaisesRegex(ValueError, "payload differs"):
            check(expected, actions, raw)
        actions, expected, raw = example("alias")
        raw["steps"][1]["nodes"].append(deepcopy(raw["steps"][1]["nodes"][1]))
        raw["steps"][1]["bindings"][1]["type"] = 6
        with self.assertRaisesRegex(ValueError, "retain declared input IDs"):
            check(expected, actions, raw)

    def test_old_immutable_node_payloads_remain_exact_even_when_unused(self):
        actions, expected, raw = example()
        for step in raw["steps"]:
            step["nodes"].append({"tag": "s", "a": 1, "b": 0, "c": 0, "name": ""})
        raw["steps"][1]["nodes"][6]["a"] = 2
        with self.assertRaisesRegex(ValueError, "immutable node payload"):
            check(expected, actions, raw)
        actions, expected, raw = example()
        raw["steps"][0]["nodes"][0]["a"] = 1
        with self.assertRaisesRegex(ValueError, "immutable node payload"):
            check(expected, actions, raw)

    def test_native_dag_and_binding_ids_have_exact_types_and_bounds(self):
        mutations = [lambda r: r["steps"][1]["bindings"][0].update(type=True),
                     lambda r: r["steps"][1]["bindings"][0].update(value=False),
                     lambda r: r["steps"][1]["bindings"][0].update(inferred=999),
                     lambda r: r["steps"][1]["nodes"][0].update(a=False),
                     lambda r: r["steps"][1]["nodes"][0].update(b=1),
                     lambda r: r["steps"][1]["nodes"].append({"tag":"a","a":6,"b":0,"c":0,"name":""}),
                     lambda r: r["steps"][1]["bindings"][0].update(extra=0),
                     lambda r: r["steps"][1]["nodes"][0].update(extra=0)]
        for mutate in mutations:
            actions, expected, raw = example()
            mutate(raw)
            with self.subTest(mutation=mutate), self.assertRaises(ValueError):
                check(expected, actions, raw)

    def test_native_rejects_missing_reordered_and_fabricated_snapshots(self):
        mutations = [lambda r: r["steps"].pop(), lambda r: r["steps"].append(deepcopy(r["steps"][-1])),
                     lambda r: r.update(steps=list(reversed(r["steps"]))),
                     lambda r: r["steps"][1].update(name="formal0"),
                     lambda r: r["steps"][1].update(outcome="observed_success")]
        for mutate in mutations:
            actions, expected, raw = example()
            mutate(raw)
            with self.subTest(mutation=mutate), self.assertRaises(ValueError):
                check(expected, actions, raw)

    def test_native_fatal_requires_exact_diagnostic_and_stops_snapshots(self):
        actions, expected, raw = example("fatal")
        diagnostic = "goose bounded checker: Invalid_scope\n"
        for status, stderr in ((0, diagnostic), (1, diagnostic), (2, ""), (2, diagnostic + "extra"),
                               (2, "goose bounded checker: Limit_exceeded\n")):
            with self.subTest(status=status, stderr=stderr), self.assertRaises(ValueError):
                check(expected, actions, raw, status, stderr)
        raw["steps"].append(deepcopy(raw["steps"][-1]))
        with self.assertRaises(ValueError):
            check(expected, actions, raw, 2, diagnostic)

    def test_native_envelope_and_json_line_framing(self):
        mutations = [lambda r: r.update(acceptance_authority=0), lambda r: r.update(success_observations=True),
                     lambda r: r.update(extra="ignored"), lambda r: r.update(status="passed"),
                     lambda r: r.update(schema="old-schema")]
        for mutate in mutations:
            actions, expected, raw = example()
            mutate(raw)
            with self.subTest(mutation=mutate), self.assertRaises(ValueError):
                check(expected, actions, raw)
        actions, expected, raw = example()
        text = json.dumps(raw)
        for bad in (text, text + "\n\n", text + "\n" + text + "\n", json.dumps(raw, indent=2) + "\n",
                    text.replace('"type": 1', '"type": 1, "type": 1', 1) + "\n"):
            with self.subTest(text=bad), self.assertRaises(ValueError):
                profile.check_trace(expected, actions, 0, bad, "")
        with self.assertRaises(ValueError):
            check(expected, actions, raw, 0, "unexpected warning")


BASE = 'fn check_definition() { return 0; }\nfn parse() { return; }\n\nfn main() {\n    print("checked");\n}\n'
EXTENDED = BASE.replace('\nfn main() {', '\nfn trace() { return; }\n\nfn main() {').replace('print("checked");', 'trace();\n    print("checked");')


def make_patch(base=BASE, result=EXTENDED):
    return "".join(difflib.unified_diff(base.splitlines(keepends=True), result.splitlines(keepends=True),
                                     fromfile="a/reference/checker.goose", tofile="b/reference/checker.goose"))


def extension_record(base, diff):
    return {"path": derivation.PATCH_PATH, "sha256": derivation.digest(diff),
            "base_derivative_sha256": derivation.digest(base),
            "preserved_checker_prefix_sha256": derivation.digest(base.split(derivation.MAIN, 1)[0] + "\n")}


class DerivationControls(unittest.TestCase):
    def test_derivation_rejects_redirected_paths_and_repository_before_commands(self):
        revision = "a" * 40
        repository = "https://github.com/example/pinned-reference.git"
        config = {"lean_ocaml": {"revision": revision, "repository": repository}}
        baseline_provenance = {
            "schema": "lean-goose.source-provenance.v2", "acceptance_authority": False,
            "replacements": deepcopy(runtime.REPLACEMENTS), "source_revision": revision,
            "source_repository": repository.removesuffix(".git"),
            "source_path": "reference/goose/benchmark.goose", "local_path": "reference/checker.goose",
        }
        changes = [
            ("local_path", "reference/decoy.goose"),
            ("local_path", "reference/../reference/checker.goose"),
            ("local_path", "/tmp/decoy.goose"),
            ("source_path", "reference/goose/decoy.goose"),
            ("source_path", "reference/checker.goose"),
            ("source_repository", "https://github.com/example/different-reference"),
        ]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            provenance_path, config_path = root / "provenance.json", root / "dependencies.json"
            config_path.write_text(json.dumps(config))
            for field, value in changes:
                provenance = deepcopy(baseline_provenance)
                provenance[field] = value
                provenance_path.write_text(json.dumps(provenance))
                with self.subTest(field=field, value=value), \
                        patch.object(runtime, "PROVENANCE", provenance_path), \
                        patch.object(runtime, "CONFIG", config_path), \
                        patch.object(runtime, "command") as command:
                    with self.assertRaisesRegex(RuntimeError,
                            "source provenance paths or repository differ from the compiled checker contract"):
                        runtime.verify_derivation(root / "unused-external-checkout")
                    command.assert_not_called()

    def test_exact_patch_reconstructs_reviewed_extension(self):
        diff = make_patch()
        self.assertEqual(derivation.apply_exact_patch(BASE, diff), EXTENDED)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root / "reference").mkdir()
            (root / derivation.PATCH_PATH).write_text(diff)
            result, facts = derivation.reconstruct(root, BASE, extension_record(BASE, diff))
            self.assertEqual(result, EXTENDED)
            self.assertTrue(facts["checking_and_parser_function_prefix_unchanged"])
            self.assertEqual(facts["sha256"], derivation.digest(diff))

    def test_digest_and_extension_path_changes_are_rejected(self):
        diff = make_patch()
        for field, value in (("sha256", "0" * 64), ("base_derivative_sha256", "0" * 64),
                             ("preserved_checker_prefix_sha256", "0" * 64),
                             ("path", "../binding-trace.patch"), ("path", "/tmp/binding-trace.patch")):
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory); (root / "reference").mkdir()
                (root / derivation.PATCH_PATH).write_text(diff)
                record = extension_record(BASE, diff); record[field] = value
                with self.subTest(field=field), self.assertRaises(ValueError):
                    derivation.reconstruct(root, BASE, record)

    def test_patch_rejects_fuzzy_paths_context_headers_and_lengths(self):
        diff = make_patch()
        lines = diff.splitlines(keepends=True)
        header = next(line for line in lines if line.startswith("@@ "))
        invalid = [diff.replace("a/reference/checker.goose", "a/reference/../reference/checker.goose", 1),
                   diff.replace("b/reference/checker.goose", "b/other.goose", 1),
                   diff.replace(" fn check_definition()", " fn changed_definition()", 1),
                   diff.replace(header, "@@ -999,1 +999,1 @@\n", 1),
                   diff.replace(header, header.replace("+1,", "+2,"), 1),
                   diff.replace(header, "@@ -1,99 +1,99 @@\n", 1),
                   diff + "".join(lines[2:]), "".join(lines[:2]), diff.rstrip("\n"),
                   diff + "--- a/other.goose\n+++ b/other.goose\n"]
        for bad in invalid:
            self.assertNotEqual(bad, diff)
            with self.subTest(patch=bad), self.assertRaises(ValueError):
                derivation.apply_exact_patch(BASE, bad)

    def test_preserved_semantic_prefix_and_main_boundary_are_enforced(self):
        for result in (EXTENDED.replace("return 0;", "return 1;", 1),
                       EXTENDED + '\nfn main() {\n}\n', EXTENDED.replace(derivation.MAIN, "\nfn renamed_main() {")):
            diff = make_patch(result=result)
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory); (root / "reference").mkdir()
                (root / derivation.PATCH_PATH).write_text(diff)
                with self.subTest(result=result), self.assertRaises(ValueError):
                    derivation.reconstruct(root, BASE, extension_record(BASE, diff))

    def test_symlink_and_parent_directory_escape_are_rejected(self):
        diff = make_patch()
        with tempfile.TemporaryDirectory() as directory, tempfile.TemporaryDirectory() as outside:
            root, external = Path(directory), Path(outside)
            (external / "binding-trace.patch").write_text(diff)
            (root / "reference").symlink_to(external, target_is_directory=True)
            with self.assertRaises(ValueError):
                derivation.reconstruct(root, BASE, extension_record(BASE, diff))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root / "reference").mkdir()
            (root / "actual.patch").write_text(diff)
            (root / derivation.PATCH_PATH).symlink_to(root / "actual.patch")
            with self.assertRaises(ValueError):
                derivation.reconstruct(root, BASE, extension_record(BASE, diff))


class QuintWireControls(unittest.TestCase):
    def test_length_framed_payloads_and_snapshots_decode_exactly(self):
        binding = [0, 2, 0, 1, 2, 0, 0, 2, 0, 1]
        wire = [0, 0, 1, *binding, 1, 0, 0, 1, 0, 0, 1, *binding]
        decoded = quint.Wire(wire).observation()
        self.assertEqual(decoded["environment"], [{"name":0,"type":[0,1],"value":[0,0],"inferred":[0,1]}])
        self.assertEqual(decoded["snapshots"], [{"name":0,"code":0,"environment":decoded["environment"]}])
        for bad in (wire[:-1], wire + [0], [2, *wire[1:]], [0, 2, *wire[2:]], [0, 0, 99]):
            with self.subTest(wire=bad), self.assertRaises(ValueError):
                quint.Wire(bad).observation()
        for bad in ([False], [-1], [1.0], "0"):
            with self.subTest(wire=bad), self.assertRaises(ValueError):
                quint.Wire(bad)

    def test_duplicate_missing_and_nonintegral_trace_identities_fail(self):
        first, second = ((0, 0, 0, 0),), ((0, 1, 0, 0),)
        left = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        right = [1, 0, 1, 0, 0, 0, 0, 0, 0, 0]
        with patch.object(quint, "PROFILE", {first, second}):
            self.assertEqual(set(quint.decode_profile(json.dumps([left, right]))), {first, second})
            for rows in ([left], [left, left], [[True, *left[1:]], right], [[1, False, *left[2:]], right],
                         [[1, 3, 1, 1, 1, *left[5:]], right]):
                with self.subTest(rows=rows), self.assertRaises(ValueError):
                    quint.decode_profile(json.dumps(rows))


def witness():
    binding = {"name": 0, "ty": [0, 1], "value": [0, 0], "inferred": [0, 1]}
    before = {"environment": [binding], "outcomes": [{"name": 0, "code": 0}], "halted": False,
              "acceptance_authority": False, "snapshots": [{"name": 0, "code": 0, "environment": [binding]}]}
    before = deepcopy(before)
    after = deepcopy(before)
    changed = dict(binding, value=[0, 999])
    after["environment"] = [deepcopy(changed)]
    after["outcomes"].append({"name": 1, "code": 6})
    after["snapshots"].append({"name": 1, "code": 6, "environment": [deepcopy(changed)]})
    return {"states": [{"s": deepcopy(before), "previous": deepcopy(before), "hasStep": False},
                       {"s": after, "previous": deepcopy(before), "hasStep": True,
                        "last": {"kind":1,"name":1,"target":0,"level":0}}]}


class CounterexampleControls(unittest.TestCase):
    TEXT = "[violation] Found an issue\nerror: Invariant violated\n"

    def check_witness(self, data, code=1, text=TEXT):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "trace.json"
            path.write_text(json.dumps(data))
            stored_gate.counterexample(code, text, path)

    def test_requires_actual_designated_payload_corruption(self):
        self.check_witness(witness())
        for code, text in ((0, self.TEXT), (2, self.TEXT), (1, "parse error")):
            with self.subTest(code=code, text=text), self.assertRaises(ValueError):
                self.check_witness(witness(), code, text)
        for mutate in (lambda r: r["states"].pop(),
                       lambda r: r["states"][1]["s"]["environment"][0].update(value=[0, 998]),
                       lambda r: r["states"][1]["previous"]["environment"][0].update(type=[0, 2]),
                       lambda r: r["states"][1]["last"].update(kind=0),
                       lambda r: r["states"][1].update(hasStep=False)):
            data = witness(); mutate(data)
            with self.subTest(mutation=mutate), self.assertRaises(ValueError):
                self.check_witness(data)

    def test_numeric_boolean_substitution_cannot_satisfy_witness(self):
        for mutate in (lambda r: r["states"][0]["s"]["environment"][0].update(name=False),
                       lambda r: r["states"][1]["last"].update(kind=True),
                       lambda r: r["states"][1]["s"]["environment"][0]["value"].__setitem__(0, False),
                       lambda r: r["states"][0]["previous"]["outcomes"][0].update(code=False)):
            data = witness(); mutate(data)
            with self.subTest(mutation=mutate), self.assertRaises(ValueError):
                self.check_witness(data)

    def test_itf_natural_numbers_are_canonical(self):
        self.assertEqual(stored_gate.itf_value({"#bigint":"999"}), 999)
        for value in ("-1", "+1", "01", "1.0", "1e2", 1, True):
            with self.subTest(value=value), self.assertRaises(ValueError):
                stored_gate.itf_value({"#bigint":value})


if __name__ == "__main__":
    unittest.main()
