"""Negative controls for exact harness derivation and transformation evidence."""
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import substitution_harness as harness
import substitution_profile as profile
import check_substitution as gate

spec = importlib.util.spec_from_file_location("substitution_quint_wire", ROOT / "formal/quint/substitution_replay.py")
quint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(quint)


def capture_example():
    """A fixed capture example observed through the compiled actual driver."""
    case = next(case for case in profile._named_cases() if case["id"] == "substitute-lambda-capture")
    row = {"decoded": True, "expressions": [[4, 0, 0, 1, 1]], "heights": [2], "loose": [1],
           "scoped": [[False, True, True, True, True, True, True]], "acceptance_authority": False}
    nodes = deepcopy(case["model_input"]["nodes"]) + [[1, 1, 0, 0, []], [4, 0, 4, 0, []]]
    return case, row, trace_for(case, nodes, 5)


def trace_for(case, nodes, result, *, error=0, fuel=profile.CHECK_FUEL):
    """Encode only a supplied raw snapshot; no transformation is calculated."""
    request = case["model_input"]
    return {"schema": profile.TRACE_SCHEMA, "engine": "goose-aot", "status": "halted" if error else "transformed",
            "operation": "lift" if request["operation"] == 0 else "substitute", "root": request["root"],
            "parameter": request["parameter"], "cutoff": request["cutoff"], "fuel_budget": fuel,
            "result": result, "error": error,
            "snapshot": {"name": "transformation", "outcome": profile.ERRORS[error] if error else "observed_success",
                         "bindings": [], "nodes": [{"tag": profile.dag.TAGS[tag], "a": a, "b": b, "c": c,
                                                     "name": bytes(name).decode("ascii")}
                                                    for tag, a, b, c, name in nodes]},
            "acceptance_authority": False}


def observe(case, row, trace, *, exit_code=0, stderr=""):
    return profile.check_native(case, row, exit_code, json.dumps(trace) + "\n", stderr)


class HarnessDerivationTests(unittest.TestCase):
    def sources(self):
        return (ROOT / harness.CHECKER).read_bytes(), (ROOT / harness.DRIVER).read_bytes()

    def test_exact_checker_round_trip_and_driver_append(self):
        checker, driver = self.sources()
        generated = harness.reconstruct(checker, driver)
        prefix, appended = generated.split(harness.SEPARATOR)
        self.assertEqual(prefix.replace(harness.RENAMED_MAIN, harness.MAIN, 1), checker)
        self.assertEqual(appended, driver)
        self.assertEqual(hashlib.sha256(checker).hexdigest(), harness.CHECKER_SHA256)
        harness.verify_generated(checker, driver, generated)

    def test_changed_checker_or_any_generated_byte_fails(self):
        checker, driver = self.sources()
        generated = harness.reconstruct(checker, driver)
        with self.assertRaises(ValueError):
            harness.reconstruct(checker.replace(b"const MAX_HEIGHT = 128", b"const MAX_HEIGHT = 129"), driver)
        for changed in (generated + b"\n", generated.replace(b"const MAX_HEIGHT = 128", b"const MAX_HEIGHT = 129"),
                        generated[:-1], generated.replace(harness.RENAMED_MAIN, harness.MAIN)):
            with self.subTest(changed=len(changed)), self.assertRaises(ValueError):
                harness.verify_generated(checker, driver, changed)

    def test_ambiguous_or_unterminated_driver_fails(self):
        checker, driver = self.sources()
        for changed in (driver + harness.MAIN, driver + harness.RENAMED_MAIN,
                        driver + harness.SEPARATOR, driver[:-1]):
            with self.subTest(driver=len(changed)), self.assertRaises(ValueError):
                harness.reconstruct(checker, changed)

    def test_generation_is_exclusive_and_hash_bound(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "diagnostic.goose"
            identity = harness.generate(ROOT, output)
            self.assertEqual(identity["generated_source_sha256"], hashlib.sha256(output.read_bytes()).hexdigest())
            self.assertEqual(identity["generated_source_bytes"], output.stat().st_size)
            self.assertFalse(identity["acceptance_authority"])
            self.assertTrue(identity["checker_bytes_preserved_except_main_identifier"])
            before = output.read_bytes()
            with self.assertRaises(ValueError):
                harness.generate(ROOT, output)
            self.assertEqual(output.read_bytes(), before)

    def test_repo_output_and_symlink_parent_into_repo_fail(self):
        with self.assertRaises(ValueError):
            harness.generate(ROOT, ROOT / "substitution-forbidden-test-output.goose")
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            link = folder / "repo-link"
            link.symlink_to(ROOT, target_is_directory=True)
            with self.assertRaises(ValueError):
                harness.generate(ROOT, link / "substitution-forbidden-test-output.goose")
            target = folder / "existing"
            target.write_text("unchanged")
            output = folder / "source.goose"
            output.symlink_to(target)
            with self.assertRaises(ValueError):
                harness.generate(ROOT, output)
            self.assertEqual(target.read_text(), "unchanged")


class InventoryTests(unittest.TestCase):
    def test_complete_graph_operation_and_control_inventory(self):
        cases = profile.cases()
        self.assertEqual(len(cases), 2546)
        self.assertEqual(len({case["id"] for case in cases}), 2546)
        finite = [case for case in cases if case["category"] == "finite"]
        self.assertEqual(len(finite), 2520)
        self.assertEqual(sum(case["model_input"]["operation"] == 0 for case in finite), 756)
        self.assertEqual(sum(case["model_input"]["operation"] == 1 for case in finite), 1764)
        self.assertEqual({node[0] for case in finite for node in case["model_input"]["nodes"]}, set(range(7)))
        self.assertEqual(sum(case["category"] == "named" for case in cases), 20)
        self.assertEqual(sum(case["category"] == "malformed" for case in cases), 6)
        for case in cases:
            self.assertEqual(json.loads(profile.encode(case)), case["model_input"])
        self.assertEqual(len(profile.native_controls()), 14)
        self.assertEqual(len(profile.ordinary_controls()), 8)

    def test_fixture_and_arguments_retain_open_root_and_replacement_ids(self):
        case, _, _ = capture_example()
        self.assertEqual(profile.native_arguments(case), ["--substitute", "2", "3", "0"])
        self.assertEqual(profile.native_fixture(case), "lean-ocaml-benchmark-dag-v1\n"
                         "n\t0\ts\t0\nn\t1\tv\t1\nn\t2\tl\t0\t1\nn\t3\tv\t0\n"
                         "d\ttransformation\t0\t0\n")

    def test_topology_refusal_is_atomic_and_not_a_process_success(self):
        row = {"decoded": False, "expressions": [], "heights": [], "loose": [], "scoped": [],
               "acceptance_authority": False}
        for case in (case for case in profile.cases() if not case["decoded"]):
            profile.validate_model(row, case)
            with self.assertRaises(ValueError):
                profile.validate_request(case["model_input"])
            observation = profile.check_native(case, row, 3, "", profile.PARSER_DIAGNOSTIC)
            self.assertIsNone(observation["trace"])
            for exit_code, stdout, stderr in ((0, "", ""), (2, "", profile.PARSER_DIAGNOSTIC),
                                              (3, "{}\n", profile.PARSER_DIAGNOSTIC)):
                with self.subTest(case=case["id"], exit_code=exit_code), self.assertRaises(ValueError):
                    profile.check_native(case, row, exit_code, stdout, stderr)
            with self.assertRaises(ValueError):
                profile.validate_model(dict(row, expressions=[[0, 0]]), case)


class ModelFramingTests(unittest.TestCase):
    def test_singleton_capture_result_and_lossless_stream(self):
        case, row, _ = capture_example()
        profile.validate_model(row, case)
        self.assertEqual(profile.decode_models(json.dumps(row) + "\n", [case]), [row])

    def test_request_rejects_wrong_ids_noncanonical_fields_and_numeric_coercion(self):
        case, _, _ = capture_example()
        mutations = [
            lambda r: r.__setitem__("operation", True), lambda r: r.__setitem__("operation", 2),
            lambda r: r.__setitem__("root", False), lambda r: r.__setitem__("root", len(r["nodes"])),
            lambda r: r.__setitem__("parameter", -1), lambda r: r.__setitem__("parameter", len(r["nodes"])),
            lambda r: r.__setitem__("cutoff", 0.0), lambda r: r.__setitem__("nodes", []),
            lambda r: r.__setitem__("extra", 0), lambda r: r["nodes"][0].__setitem__(0, False),
            lambda r: r["nodes"][0].__setitem__(2, 1), lambda r: r["depths"].__setitem__(0, False),
        ]
        for mutation in mutations:
            request = deepcopy(case["model_input"])
            mutation(request)
            with self.subTest(request=request), self.assertRaises(ValueError):
                profile.validate_request(request)

    def test_model_rejects_bool_numbers_unknown_fields_and_multiple_results(self):
        case, row, _ = capture_example()
        mutations = [
            lambda r: r.__setitem__("decoded", 1), lambda r: r.__setitem__("acceptance_authority", 0),
            lambda r: r.__setitem__("extra", 0), lambda r: r.__delitem__("loose"),
            lambda r: r["expressions"].append([0, 0]), lambda r: r["expressions"][0].__setitem__(0, False),
            lambda r: r["heights"].__setitem__(0, True), lambda r: r["heights"].__setitem__(0, 0),
            lambda r: r["loose"].__setitem__(0, False), lambda r: r["scoped"][0].__setitem__(0, 0),
            lambda r: r["scoped"][0].pop(),
        ]
        for mutation in mutations:
            changed = deepcopy(row)
            mutation(changed)
            with self.subTest(row=changed), self.assertRaises(ValueError):
                profile.validate_model(changed, case)

    def test_prefix_wire_rejects_truncation_trailing_data_and_invalid_name(self):
        case, row, _ = capture_example()
        for wire in ([], [7], [0], [1], [4, 0, 0], [4, 0, 0, 1, 1, 0],
                     [2, 0], [2, 1, 233], [2, 1, 45], [2, 2, 65], [2, 1, True]):
            with self.subTest(wire=wire), self.assertRaises(ValueError):
                profile.validate_model(dict(row, expressions=[wire]), case)

    def test_json_stream_rejects_missing_extra_duplicate_and_nonfinite_results(self):
        case, row, _ = capture_example()
        text = json.dumps(row)
        for changed in (text, text + "\n" + text + "\n", "\n", text[:-1] + ',"decoded":true}\n',
                        text.replace('"heights": [2]', '"heights": [NaN]') + "\n"):
            with self.subTest(text=changed[:80]), self.assertRaises(ValueError):
                profile.decode_models(changed, [case])


class NativeCorrespondenceTests(unittest.TestCase):
    def test_actual_capture_result_keeps_original_raw_prefix(self):
        case, row, trace = capture_example()
        observation = observe(case, row, trace)
        self.assertTrue(observation["result_wire_matched"])
        self.assertTrue(observation["input_prefix_preserved"])
        self.assertEqual(observation["node_payloads"], 6)

    def test_capture_or_wrong_result_cannot_match_agreed_model(self):
        case, row, trace = capture_example()
        changed = deepcopy(trace)
        changed["snapshot"]["nodes"][4]["a"] = 0
        with self.assertRaises(ValueError):
            observe(case, row, changed)
        for result in (True, -1, 6, None, 0):
            with self.subTest(result=result), self.assertRaises(ValueError):
                observe(case, row, dict(trace, result=result))

    def test_imported_unused_nodes_and_raw_arguments_cannot_change(self):
        case, row, trace = capture_example()
        mutations = [
            lambda t: t.__setitem__("root", 1), lambda t: t.__setitem__("parameter", 1),
            lambda t: t.__setitem__("cutoff", 1), lambda t: t.__setitem__("root", True),
            lambda t: t.__setitem__("operation", "lift"), lambda t: t.__setitem__("fuel_budget", 100),
            lambda t: t["snapshot"]["nodes"][3].__setitem__("a", 1),
            lambda t: t["snapshot"]["nodes"][2].__setitem__("a", 3),
            lambda t: t["snapshot"]["nodes"][4].__setitem__("normal", -1),
            lambda t: t["snapshot"]["nodes"][5].__setitem__("b", 5),
        ]
        for mutation in mutations:
            changed = deepcopy(trace)
            mutation(changed)
            with self.subTest(trace=changed), self.assertRaises(ValueError):
                observe(case, row, changed)

    def test_original_replacement_id_is_checked_even_for_equal_payloads(self):
        case = next(case for case in profile._named_cases() if case["id"] == "substitute-original-replacement-id")
        row = {"decoded": True, "expressions": [[1, 2]], "heights": [1], "loose": [3],
               "scoped": [[False, False, False, True, True, True, True]], "acceptance_authority": False}
        trace = trace_for(case, case["model_input"]["nodes"], 2)
        observe(case, row, trace)
        with self.assertRaises(ValueError):
            observe(case, row, dict(trace, result=1))

    def test_envelope_authority_snapshot_and_process_contract_are_strict(self):
        case, row, trace = capture_example()
        mutations = [
            lambda t: t.__setitem__("acceptance_authority", 0), lambda t: t.__setitem__("error", False),
            lambda t: t.__setitem__("status", "checked"), lambda t: t.__setitem__("extra", 0),
            lambda t: t["snapshot"].__setitem__("outcome", "Type_mismatch"),
            lambda t: t["snapshot"].__setitem__("name", "different"),
            lambda t: t["snapshot"]["bindings"].append({"name": "inserted", "type": 0, "value": 0, "inferred": 0}),
        ]
        for mutation in mutations:
            changed = deepcopy(trace)
            mutation(changed)
            with self.subTest(trace=changed), self.assertRaises(ValueError):
                observe(case, row, changed)
        for exit_code, stdout, stderr in ((True, json.dumps(trace) + "\n", ""), (0, json.dumps(trace), ""),
                                        (0, json.dumps(trace) + "\n", "unexpected\n"), (2, "", "")):
            with self.subTest(exit_code=exit_code, stderr=stderr), self.assertRaises(ValueError):
                profile.check_native(case, row, exit_code, stdout, stderr)

    def test_resource_refusal_has_null_result_and_cannot_satisfy_a_pure_prediction(self):
        control = next(control for control in profile.native_controls() if control["id"] == "operation-fuel-zero")
        case = control["case"]
        trace = trace_for(case, case["model_input"]["nodes"], None, error=7, fuel=0)
        observation = profile.check_control(control, 2, json.dumps(trace) + "\n", control["stderr"])
        self.assertFalse(observation["pure_model_result"])
        self.assertIsNone(observation["trace"]["result"])
        for changed in (dict(trace, result=0), dict(trace, error=0), dict(trace, status="transformed")):
            with self.subTest(trace=changed), self.assertRaises(ValueError):
                profile.check_control(control, 2, json.dumps(changed) + "\n", control["stderr"])
        row = {"decoded": True, "expressions": [[1, 1]], "heights": [1], "loose": [2],
               "scoped": [[False, False, True, True, True, True, True]], "acceptance_authority": False}
        with self.assertRaises(ValueError):
            profile.check_native(case, row, 2, json.dumps(trace) + "\n", control["stderr"])

    def test_parser_import_envelope_refusals_cannot_emit_partial_json(self):
        for control in (control for control in profile.native_controls() if not control["envelope"]):
            profile.check_control(control, control["exit_code"], "", control["stderr"])
            with self.subTest(control=control["id"]), self.assertRaises(ValueError):
                profile.check_control(control, control["exit_code"], "{}\n", control["stderr"])

    def test_ordinary_scope_halt_suppresses_check_receipt(self):
        control = next(control for control in profile.ordinary_controls() if control["outcomes"] == ["Invalid_scope"])
        result = profile.check_ordinary(control, "--check", 2, "", profile.dag.SCOPE_DIAGNOSTIC)
        self.assertFalse(result["completed_receipt"])
        with self.assertRaises(ValueError):
            profile.check_ordinary(control, "--check", 2, "{}\n", profile.dag.SCOPE_DIAGNOSTIC)


class QuintAdapterTests(unittest.TestCase):
    @staticmethod
    def wire(index, request, observation):
        result = quint.identity(index, request) + [int(observation["decoded"]), 0, len(observation["expressions"])]
        for expression, height, loose, scoped in zip(observation["expressions"], observation["heights"],
                                                     observation["loose"], observation["scoped"]):
            result.extend([len(expression), *expression, height, loose, len(scoped), *map(int, scoped)])
        return result

    def test_general_depth_lists_preserve_order_and_multiplicity(self):
        case, _, _ = capture_example()
        request = deepcopy(case["model_input"])
        for depths in ([], [6, 0, 6, 2]):
            request["depths"] = depths
            self.assertEqual(quint.request(json.dumps(request)), request)

    def test_malformed_topology_is_decided_by_quint_not_adapter(self):
        case = next(case for case in profile.cases() if not case["decoded"])
        request = quint.request(profile.encode(case))
        row = quint.Wire(quint.identity(0, request) + [0, 0, 0]).observation(0, request)
        profile.validate_model(row, case)

    def test_request_fields_are_exact_and_in_range(self):
        case, _, _ = capture_example()
        text = profile.encode(case)
        invalid = [text[:-1] + ',"root":2}', text.replace('"root":2', '"root":true'),
                   text.replace('"cutoff":0', '"cutoff":NaN'), text.replace('"operation":1', '"operation":2'),
                   text.replace('"root":2', '"root":4'), text.replace('"parameter":3', '"parameter":4'),
                   text.replace('"cutoff":0', '"cutoff":-1')]
        for changed in invalid:
            with self.subTest(text=changed), self.assertRaises(ValueError):
                quint.request(changed)

    def test_result_identity_covers_operation_and_every_argument(self):
        case, row, _ = capture_example()
        request = case["model_input"]
        wire = self.wire(0, request, row)
        self.assertEqual(quint.Wire(wire).observation(0, request), row)
        identity_size = len(quint.identity(0, request))
        for position in range(identity_size):
            changed = list(wire)
            changed[position] += 1
            with self.subTest(position=position), self.assertRaises(ValueError):
                quint.Wire(changed).observation(0, request)

    def test_result_framing_rejects_missing_extra_boolean_and_partial_roots(self):
        case, row, _ = capture_example()
        request = case["model_input"]
        wire = self.wire(0, request, row)
        size = len(quint.identity(0, request))
        invalid = [wire[:-1], wire + [0]]
        for position, value in ((0, True), (size, 2), (size + 1, 1), (size + 2, 0),
                                (size + 2, 2), (size + 3, 100000), (len(wire) - 1, 2)):
            changed = list(wire)
            changed[position] = value
            invalid.append(changed)
        for changed in invalid:
            with self.subTest(wire=changed), self.assertRaises(ValueError):
                quint.Wire(changed).observation(0, request)

    def test_batch_identity_rejects_reordering_duplication_and_trailing_batches(self):
        case, row, _ = capture_example()
        request = case["model_input"]
        first, second = self.wire(0, request, row), self.wire(1, request, row)
        with patch.object(quint, "BATCH_SIZE", 1):
            good = json.dumps([first]) + "\n" + json.dumps([second]) + "\n"
            self.assertEqual(quint.decode_batches(good, [request, request]), [row, row])
            invalid = [json.dumps([first]), json.dumps([second]) + "\n" + json.dumps([first]),
                       json.dumps([first]) + "\n" + json.dumps([first]), good + json.dumps([second]),
                       json.dumps([first, second])]
            for changed in invalid:
                with self.subTest(text=changed[:80]), self.assertRaises(ValueError):
                    quint.decode_batches(changed, [request, request])


def capture_witness():
    """The fixed two-state unlifted-replacement witness from actual Quint."""
    query = {"nodes": [
        {"tag": 0, "a": 0, "b": 0, "c": 0, "name": []},
        {"tag": 1, "a": 0, "b": 0, "c": 0, "name": []},
        {"tag": 1, "a": 1, "b": 0, "c": 0, "name": []},
        {"tag": 4, "a": 0, "b": 2, "c": 0, "name": []}],
        "operation": 1, "root": 3, "parameter": 1, "cutoff": 0}
    before = {"decoded": True, "acceptance_authority": False,
              "rows": [{"expression": [4, 0, 0, 1, 1], "height": 2, "loose": 1}]}
    after = {"decoded": True, "acceptance_authority": False,
             "rows": [{"expression": [4, 0, 0, 1, 0], "height": 2, "loose": 0}]}
    return {"#meta": {"format": "ITF", "source": "Substitution.qnt", "status": "violation"},
            "vars": ["q", "observed"],
            "states": [{"#meta": {"index": 0}, "q": deepcopy(query), "observed": before},
                       {"#meta": {"index": 1}, "q": deepcopy(query), "observed": after}]}


class CounterexampleTests(unittest.TestCase):
    diagnostic = "[violation] Found an issue\nerror: Invariant violated\n"

    def test_designated_capture_witness_requires_exact_process_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "counterexample.json"
            path.write_text(json.dumps(capture_witness()))
            gate.counterexample(1, self.diagnostic, path)
            for exit_code, text in ((0, self.diagnostic), (True, self.diagnostic),
                                    (2, self.diagnostic), (1, "[violation] Found an issue\n"),
                                    (1, "error: Invariant violated\n"), (1, "typecheck failed\n")):
                with self.subTest(exit_code=exit_code, text=text), self.assertRaises(ValueError):
                    gate.counterexample(exit_code, text, path)

    def test_counterexample_rejects_different_query_result_or_trace(self):
        mutations = [
            lambda w: w["#meta"].__setitem__("status", "ok"),
            lambda w: w["#meta"].__setitem__("source", "Different.qnt"),
            lambda w: w["vars"].append("extra"),
            lambda w: w["states"][0].__setitem__("extra", 0),
            lambda w: w["states"][1]["#meta"].__setitem__("index", True),
            lambda w: w["states"][0]["q"].__setitem__("operation", 0),
            lambda w: w["states"][1]["q"].__setitem__("parameter", 2),
            lambda w: w["states"][1]["q"].__setitem__("cutoff", False),
            lambda w: w["states"][0]["q"]["nodes"][2].__setitem__("a", True),
            lambda w: w["states"][1]["observed"]["rows"][0].__setitem__("expression", [4, 0, 0, 1, 1]),
            lambda w: w["states"][1]["observed"]["rows"][0].__setitem__("loose", 1),
            lambda w: w["states"][0]["observed"]["rows"][0].__setitem__("height", 3),
            lambda w: w["states"][1]["observed"].__setitem__("acceptance_authority", 0),
            lambda w: w["states"].reverse(), lambda w: w["states"].pop(),
            lambda w: w["states"].append(deepcopy(w["states"][-1])),
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "counterexample.json"
            for mutation in mutations:
                witness = capture_witness()
                mutation(witness)
                path.write_text(json.dumps(witness))
                with self.subTest(witness=witness), self.assertRaises(ValueError):
                    gate.counterexample(1, self.diagnostic, path)


if __name__ == "__main__":
    unittest.main()
