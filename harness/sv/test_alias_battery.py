#!/usr/bin/env python3
"""Consistency of the `always_comb` alias-guard battery (WP4 round 6, lane B).

    python3 harness/sv/test_alias_battery.py

No Lean and no simulator: this pins the DATA the guard's rows are made of, so
a row cannot drift from its fixture, its declaration or its documentation
unnoticed. The guard itself (`LeanModels/Sv/CombAlias2.lean`) is exercised by
`diff_test2.py` on these rows and by the `#guard` pins and theorems of
`CombAlias2.lean`, `CombAlias2Sound.lean` and `CombAlias2Example.lean`.

What is checked:

  * every `acg_alias_*` row has a fixture directory (`.sv` + `.sv.json`), the
    envelope is the one the source hashes to, and the source file is the one
    the envelope names;
  * the REFUSED half (assign, port loop, chain, `~` copy, bit-level, inside an
    instance, through a child's own assign) are loud-refusal rows of kind
    `AlwaysComb:alias-read`, each with a `measured` field that names the
    simulators; `acg_alias_wire` is a loud-refusal row of the extractor's
    `NetSymbol:net-z` (an internal wire never reaches the guard) and its
    envelope carries that kind;
  * the ADMITTED half (write-then-read, separate always_comb copy, a copy of
    what the block does not write, bit-disjoint, port-loop and instance
    write-then-read) are simulated rows: no `refusal`, no declaration;
  * the two retired declarations are gone from every row, `acg_xproc_bits`
    keeps its declaration with the tightened text, and the documentation names
    all of it.
"""

import hashlib
import json
import os
import re
import unittest

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CASES = os.path.join(REPO, "harness", "sv", "cases2.json")
GOLDEN = os.path.join(REPO, "harness", "sv", "xcelium_golden.json")
SEM2 = os.path.join(REPO, "Examples", "system-verilog", "sem2")
ORACLE_DOC = os.path.join(REPO, "docs", "sv-oracle-disagreements.md")

KIND = "AlwaysComb:alias-read"
REFUSED = ["acg_alias_assign", "acg_alias_port", "acg_alias_chain", "acg_alias_not",
           "acg_alias_bits", "acg_alias_hier", "acg_alias_thru"]
NET_REFUSED = "acg_alias_wire"
ADMITTED = ["acg_alias_wr", "acg_alias_copy", "acg_alias_far", "acg_alias_bits_ok",
            "acg_alias_port_wr", "acg_alias_hier_ok"]
RETIRED_IDS = ["iverilog-comb-assign-alias-sensitivity", "iverilog-comb-port-loop-sensitivity"]
XPROC = "acg_xproc_bits"
XPROC_ID = "iverilog-comb-bit-split-sensitivity"


def load_cases():
    with open(CASES, encoding="utf-8") as handle:
        return {c["name"]: c for c in json.load(handle)["cases"]}


def fixture_paths(name):
    d = os.path.join(SEM2, name)
    return os.path.join(d, name + ".sv"), os.path.join(d, name + ".sv.json")


def envelope_kinds(path):
    found = set()

    def walk(node):
        if isinstance(node, dict):
            if node.get("kind") == "Unsupported" and isinstance(node.get("sv_kind"), str):
                found.add(node["sv_kind"])
            for value in node.values():
                walk(value)
        elif isinstance(node, list):
            for value in node:
                walk(value)

    with open(path, encoding="utf-8") as handle:
        walk(json.load(handle))
    return found


class AliasBattery(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases = load_cases()

    def test_every_alias_fixture_has_a_row_and_back(self):
        on_disk = sorted(n for n in os.listdir(SEM2) if n.startswith("acg_alias_"))
        in_rows = sorted(n for n in self.cases if n.startswith("acg_alias_"))
        expected = sorted(REFUSED + [NET_REFUSED] + ADMITTED)
        self.assertEqual(on_disk, expected)
        self.assertEqual(in_rows, expected)

    def test_fixtures_are_fresh_and_self_consistent(self):
        for name in REFUSED + [NET_REFUSED] + ADMITTED:
            sv, env = fixture_paths(name)
            self.assertTrue(os.path.isfile(sv), sv)
            self.assertTrue(os.path.isfile(env), env)
            with open(sv, "rb") as handle:
                digest = hashlib.sha256(handle.read()).hexdigest()
            with open(env, encoding="utf-8") as handle:
                doc = json.load(handle)
            self.assertEqual(doc["schema_version"], "sv-0.2", name)
            self.assertEqual(doc["top"], name)
            recorded = {f["path"]: f["sha256"] for f in doc["source_files"]}
            rel = os.path.relpath(sv, REPO)
            self.assertEqual(recorded.get(rel), digest,
                             "%s: the envelope does not hash the source it names (re-extract)" % name)
            case = self.cases[name]
            self.assertEqual(case["example"], "sem2/" + name)
            self.assertEqual(case["top"], name)

    def test_refused_rows_are_loud_with_a_measured_field(self):
        for name in REFUSED:
            case = self.cases[name]
            self.assertEqual(case.get("refusal"), KIND, name)
            self.assertNotIn("oracle_disagreement", case, name)
            measured = case.get("measured", "")
            for needle in ("Icarus", "Xcelium", "Verilator", "CombAlias2.lean"):
                self.assertIn(needle, measured, "%s: measured field lacks %r" % (name, needle))
            self.assertTrue(case["stimulus"], name)

    def test_internal_wire_is_refused_by_the_extractor_not_the_guard(self):
        case = self.cases[NET_REFUSED]
        self.assertEqual(case.get("refusal"), "NetSymbol:net-z")
        self.assertIn("NOT REFUSED BY THE ALIAS GUARD", case.get("measured", ""))
        self.assertIn("NetSymbol:net-z", envelope_kinds(fixture_paths(NET_REFUSED)[1]))

    def test_admitted_rows_are_simulated_and_undeclared(self):
        for name in ADMITTED:
            case = self.cases[name]
            self.assertNotIn("refusal", case, name)
            self.assertNotIn("oracle_disagreement", case, name)
            self.assertNotIn("icarus_unavailable", case, name)
            self.assertTrue(case["stimulus"], name)
            self.assertFalse(envelope_kinds(fixture_paths(name)[1]), name)

    def test_retired_declarations_are_gone_and_the_bit_split_one_stays(self):
        ids = {}
        for name, case in self.cases.items():
            decl = case.get("oracle_disagreement")
            if decl:
                ids.setdefault(decl.get("id"), []).append(name)
        for retired in RETIRED_IDS:
            self.assertNotIn(retired, ids)
        self.assertEqual(ids.get(XPROC_ID), [XPROC])
        decl = self.cases[XPROC]["oracle_disagreement"]
        self.assertEqual(decl["sim"], "iverilog")
        self.assertIn("6.5", decl["reference"])
        self.assertIn("independent element", decl["reference"])
        self.assertIn("WHOLE-VECTOR", decl["observed"])
        for read in ("y = t", "y = t[1:0]", "y = t[0]", "y = {t[1], t[0]}"):
            self.assertIn(read, decl["observed"])

    def test_admitted_rows_are_pinned_to_the_reference(self):
        with open(GOLDEN, encoding="utf-8") as handle:
            rows = json.load(handle)["rows"]
        for name in ADMITTED:
            self.assertIn(name, rows, "%s has no pinned Xcelium trace" % name)
            self.assertEqual(rows[name]["status"], "ok", name)
            self.assertEqual(len(rows[name]["cycles"]), len(self.cases[name]["stimulus"]), name)

    def test_documentation_names_everything(self):
        with open(ORACLE_DOC, encoding="utf-8") as handle:
            doc = handle.read()
        for name in REFUSED + [NET_REFUSED] + ADMITTED:
            self.assertIn("`%s`" % name, doc, name)
        for retired in RETIRED_IDS:
            self.assertRegex(doc, r"\|\s*`%s`\s*\|" % re.escape(retired))
        self.assertIn(KIND, doc)
        self.assertNotIn("@@", doc)


if __name__ == "__main__":
    unittest.main()
