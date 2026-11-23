"""Adversarial framing controls for the authored semantic-history counterexample.

This independent specimen contains explicit two/three-binding histories and
expected certificate fields; it does not import the validator's expectations or
derive them from a Quint trace. Actual Quint execution belongs to the formal gate.
"""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from semantic_environment_negative import counterexample

VIOLATION = "[violation] Found an issue (1ms).\nerror: Invariant violated\n"


def specimen():
    bindings = [
        {"name": [85], "ty": [0, 2], "value": [0, 1], "inferred": [0, 2]},
        {"name": [105, 100], "ty": [5, 2, 1, 85, 2, 1, 85],
         "value": [4, 2, 1, 85, 1, 0], "inferred": [5, 0, 1, 0, 1]},
        {"name": [86], "ty": [0, 2], "value": [2, 1, 85], "inferred": [0, 2]},
    ]
    semantic_fields = [
        ([0, 3], [0, 2], [0, 2], [0, 2], [0, 2]),
        ([0, 2], [5, 2, 1, 85, 2, 1, 85], [5, 0, 1, 0, 1], [5, 0, 1, 0, 1], [5, 0, 1, 0, 1]),
        ([0, 3], [0, 2], [0, 2], [0, 2], [0, 2]),
    ]
    certificates = []
    snapshots = []
    for index, binding in enumerate(bindings):
        certificate = {"predecessor": deepcopy(bindings[:index]), "stored": deepcopy(binding), "fuel": 128}
        for name, value in zip(("declaredSort", "valueType", "normalizedType", "inferredNormal", "declaredNormal"),
                               semantic_fields[index]):
            certificate[name] = {"value": value, "code": 0}
        certificates.append(certificate)
        snapshots.append({"name": binding["name"], "code": 0, "bindings": deepcopy(bindings[:index + 1])})
    before = {"checked": {"environment": deepcopy(bindings[:2]), "snapshots": deepcopy(snapshots[:2]),
                          "halted": False, "acceptance_authority": False},
              "certificates": deepcopy(certificates[:2])}
    after = {"checked": {"environment": deepcopy(bindings), "snapshots": snapshots,
                         "halted": False, "acceptance_authority": False}, "certificates": certificates}
    after["checked"]["environment"][0]["value"] = [0, 0]
    after["checked"]["snapshots"][2]["bindings"][0]["value"] = [0, 0]
    return {
        "#meta": {"source": "SemanticEnvironment.qnt", "status": "violation", "format": "ITF"},
        "vars": ["s", "previous", "last", "hasStep"],
        "states": [
            {"#meta": {"index": 0}, "s": deepcopy(before), "previous": deepcopy(before),
             "last": {"name": [85], "ty": [0, 2], "value": [0, 1], "fuel": 128}, "hasStep": False},
            {"#meta": {"index": 1}, "s": after, "previous": deepcopy(before),
             "last": {"name": [86], "ty": [0, 2], "value": [2, 1, 85], "fuel": 128}, "hasStep": True},
        ],
    }


def encode_itf(value):
    if type(value) is int:
        return {"#bigint": str(value)}
    if isinstance(value, list):
        return [encode_itf(item) for item in value]
    if isinstance(value, dict):
        return {key: encode_itf(item) for key, item in value.items()}
    return value


class SemanticEnvironmentNegativeControls(unittest.TestCase):
    def check(self, witness, *, exit_code=1, text=VIOLATION, raw=None):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "negative.itf.json"
            path.write_text(json.dumps(encode_itf(witness)) if raw is None else raw, encoding="utf-8")
            counterexample(exit_code, text, path)

    def rejects(self, mutate):
        witness = specimen()
        mutate(witness)
        with self.assertRaises(ValueError):
            self.check(witness)

    def test_exact_authored_negative_witness_is_accepted(self):
        self.check(specimen())

    def test_process_must_report_designated_invariant_failure(self):
        for code in (0, 2, -1, True, 1.0, "1"):
            with self.subTest(exit_code=code), self.assertRaises(ValueError):
                self.check(specimen(), exit_code=code)
        for text in ("", "error: Invariant violated", "[violation] Found an issue",
                     "error: Type error", "[ok] No violation found", None):
            with self.subTest(text=text), self.assertRaises(ValueError):
                self.check(specimen(), text=text)

    def test_source_and_state_inventory_are_exact(self):
        mutations = [lambda w: w["#meta"].update(source="TypingConversion.qnt"),
                     lambda w: w["#meta"].update(source="formal/quint/SemanticEnvironment.qnt"),
                     lambda w: w["#meta"].update(status="ok"), lambda w: w["#meta"].update(format="JSON"),
                     lambda w: w.update(extra=True), lambda w: w.update(**{"#meta": []}),
                     lambda w: w["vars"].reverse(), lambda w: w["states"].reverse(),
                     lambda w: w["states"].pop(), lambda w: w["states"].append(deepcopy(w["states"][1])),
                     lambda w: w["states"][0].update(extra=False),
                     lambda w: w["states"][1]["#meta"].update(index=0)]
        for index, mutate in enumerate(mutations):
            with self.subTest(mutation=index):
                self.rejects(mutate)

    def test_generic_corruption_or_no_corruption_is_not_this_witness(self):
        for value in ([0, 1], [0, 999], [1, 0], [0, -1]):
            with self.subTest(value=value):
                def mutate(w):
                    state = w["states"][1]["s"]["checked"]
                    state["environment"][0]["value"] = value
                    state["snapshots"][2]["bindings"][0]["value"] = value
                self.rejects(mutate)
        self.rejects(lambda w: w["states"][1]["s"]["checked"]["environment"][0].update(inferred=[0, 0]))
        self.rejects(lambda w: w["states"][1]["s"]["checked"]["environment"][1].update(value=[0, 0]))

    def test_old_certificates_cannot_be_repaired_rewritten_or_dropped(self):
        mutations = [lambda w: w["states"][1]["s"]["certificates"][0]["stored"].update(value=[0, 0]),
                     lambda w: w["states"][1]["s"]["certificates"][1]["predecessor"][0].update(value=[0, 0]),
                     lambda w: w["states"][1]["s"]["certificates"][0].update(fuel=127),
                     lambda w: w["states"][1]["s"]["certificates"].pop(0),
                     lambda w: w["states"][1]["s"]["certificates"].reverse()]
        for index, mutate in enumerate(mutations):
            with self.subTest(mutation=index):
                self.rejects(mutate)

    def test_each_semantic_certificate_result_is_checked(self):
        for field in ("declaredSort", "valueType", "normalizedType", "inferredNormal", "declaredNormal"):
            for index in range(3):
                with self.subTest(certificate=index, field=field):
                    self.rejects(lambda w: w["states"][1]["s"]["certificates"][index][field].update(value=[0, 42]))
                    self.rejects(lambda w: w["states"][1]["s"]["certificates"][index][field].update(code=9))

    def test_predecessors_and_old_snapshots_are_frozen(self):
        mutations = [lambda w: w["states"][1]["previous"]["checked"]["environment"][0].update(value=[0, 0]),
                     lambda w: w["states"][0]["s"]["checked"]["environment"].clear(),
                     lambda w: w["states"][1]["s"]["checked"]["snapshots"][0]["bindings"][0].update(value=[0, 0]),
                     lambda w: w["states"][1]["s"]["checked"]["snapshots"][1]["bindings"][0].update(value=[0, 0]),
                     lambda w: w["states"][1]["s"]["certificates"][2]["predecessor"][0].update(value=[0, 0]),
                     lambda w: w["states"][1]["s"]["certificates"][2]["predecessor"].reverse()]
        for index, mutate in enumerate(mutations):
            with self.subTest(mutation=index):
                self.rejects(mutate)

    def test_third_insertion_and_latest_snapshot_cannot_be_forged(self):
        mutations = [lambda w: w["states"][1]["s"]["checked"]["environment"].pop(),
                     lambda w: w["states"][1]["s"]["certificates"].pop(),
                     lambda w: w["states"][1]["s"]["checked"]["snapshots"].pop(),
                     lambda w: w["states"][1]["s"]["checked"]["snapshots"][2].update(code=6),
                     lambda w: w["states"][1]["s"]["checked"]["snapshots"][2]["bindings"][0].update(value=[0, 1]),
                     lambda w: w["states"][1]["s"]["checked"]["environment"][2].update(value=[0, 1]),
                     lambda w: w["states"][1]["last"].update(name=[85]),
                     lambda w: w["states"][1]["s"]["checked"].update(halted=True),
                     lambda w: w["states"][1]["s"]["checked"].update(acceptance_authority=True)]
        for index, mutate in enumerate(mutations):
            with self.subTest(mutation=index):
                self.rejects(mutate)

    def test_booleans_floats_and_naturals_cannot_coerce_equal(self):
        mutations = [lambda w: w["states"][0].update(hasStep=0),
                     lambda w: w["states"][1].update(hasStep=1),
                     lambda w: w["states"][1]["#meta"].update(index=True),
                     lambda w: w["states"][1]["s"]["checked"].update(halted=0),
                     lambda w: w["states"][1]["s"]["checked"]["environment"][0].update(value=[False, 0]),
                     lambda w: w["states"][1]["s"]["checked"]["environment"][0].update(value=[0, 0.0]),
                     lambda w: w["states"][1]["s"]["certificates"][0]["declaredSort"].update(code=False),
                     lambda w: w["states"][1]["s"]["certificates"][0].update(fuel=128.0)]
        for index, mutate in enumerate(mutations):
            with self.subTest(mutation=index):
                self.rejects(mutate)

    def test_malformed_json_and_bigints_fail_closed(self):
        good = json.dumps(encode_itf(specimen()))
        malformed = ["", "{", "[]", '{"#bigint":"1"}', good + good,
                     good.replace('"status": "violation"', '"status": "violation", "status": "violation"', 1),
                     good.replace('"#bigint": "128"', '"#bigint": "0128"', 1),
                     good.replace('"#bigint": "128"', '"#bigint": "-1"', 1),
                     good.replace('"#bigint": "128"', '"#bigint": true', 1),
                     good.replace('"#bigint": "128"', '"#bigint": NaN', 1),
                     good.replace('"#bigint": "128"', '"#bigint": "128.0"', 1)]
        for index, raw in enumerate(malformed):
            with self.subTest(mutation=index), self.assertRaises(ValueError):
                self.check(specimen(), raw=raw)


if __name__ == "__main__":
    unittest.main()
