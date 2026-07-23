#!/usr/bin/env python3
"""Unit tests for extractors/spice/extract.py (schema spice-0.1).

Run from the repo root:  python3 extractors/spice/test_extract.py

Covers: exact suffix/decimal value parsing (the normative table in
docs/spice-envelope-schema.md), logical-line assembly (title, comments,
continuations, .end), the M0 card vocabulary, .subckt/.ends nesting and
error demotion, Unsupported routing, and byte-identical double runs on
the committed Examples/spice/{divider,chain,r2r} netlists.
"""

import json
import os
import sys
import unittest
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import extract  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def env_of(deck):
    return extract.extract_source(deck, "test.cir", deck.encode())


def cards_of(deck):
    return env_of(deck)["netlist"]["cards"]


class TestValueParsing(unittest.TestCase):
    CASES = [
        # (token, num, den) -- the normative examples first
        ("1k", 1000, 1),
        ("1m", 1, 1000),
        ("2.2meg", 2200000, 1),
        ("470u", 47, 100000),
        ("1.5", 3, 2),
        # decimals are exact, never float
        ("2.2", 11, 5),
        ("0.1", 1, 10),
        (".5", 1, 2),
        ("5.", 5, 1),
        ("3.14159", 314159, 100000),
        # every suffix, case-insensitivity (M is milli even uppercase!)
        ("1T", 10**12, 1),
        ("1g", 10**9, 1),
        ("2K", 2000, 1),
        ("1M", 1, 1000),
        ("1MEG", 10**6, 1),
        ("1Meg", 10**6, 1),
        ("3.3n", 33, 10**10),
        ("2p", 1, 5 * 10**11),
        ("1f", 1, 10**15),
        ("1mil", 127, 5000000),  # 25.4e-6 exactly
        # units after the suffix (and bare units) are ignored
        ("1kohm", 1000, 1),
        ("5V", 5, 1),
        ("100nF", 1, 10**7),
        ("2.2megohm", 2200000, 1),
        # exponents, signs
        ("1e3", 1000, 1),
        ("1.5e-2", 3, 200),
        ("-4.7k", -4700, 1),
        ("+0.25", 1, 4),
        ("-1E-3", -1, 1000),
        ("2e3k", 2 * 10**6, 1),  # exponent and suffix compose
        ("1e", 1, 1),  # bare 'e' is a unit letter, not an exponent (ngspice)
        ("0", 0, 1),
    ]

    def test_exact_values(self):
        for tok, num, den in self.CASES:
            got = extract.parse_value(tok)
            self.assertIsNotNone(got, tok)
            self.assertEqual(got, Fraction(num, den), tok)

    def test_rejects_non_numbers(self):
        for tok in ["abc", "", "1..2", "--3", "k1", "1k3", "1e+",
                    ".", "3 3", "0x10", "1.2.3"]:
            self.assertIsNone(extract.parse_value(tok), tok)

    def test_value_json_lowest_terms(self):
        self.assertEqual(extract.value_json(Fraction(470, 10**6)),
                         {"num": 47, "den": 100000})


class TestLogicalLines(unittest.TestCase):
    def test_title_comments_continuation_end(self):
        deck = ("my title line\n"
                "* full-line comment\n"
                "r1 a b\n"
                "+ 1k   ; inline comment\n"
                "\n"
                "r2 b 0 2k $ dollar comment\n"
                ".end\n"
                "r3 ignored after end 1k\n")
        env = env_of(deck)
        self.assertEqual(env["netlist"]["title"], "my title line")
        cards = env["netlist"]["cards"]
        self.assertEqual([c["kind"] for c in cards], ["R", "R"])
        self.assertEqual(cards[0]["value"], {"num": 1000, "den": 1})
        self.assertEqual(cards[0]["span"], {"line": 3, "end_line": 4})
        self.assertEqual(cards[1]["value"], {"num": 2000, "den": 1})

    def test_first_line_is_always_title(self):
        # the classic SPICE gotcha: a card on line 1 is swallowed as title
        env = env_of("r1 a b 1k\nr2 b 0 2k\n")
        self.assertEqual(env["netlist"]["title"], "r1 a b 1k")
        self.assertEqual(len(env["netlist"]["cards"]), 1)

    def test_stray_continuation(self):
        (c,) = cards_of("t\n+ 1k\n")
        self.assertEqual(c["kind"], "Unsupported")
        self.assertEqual(c["spice_kind"], "Continuation:stray")


class TestCards(unittest.TestCase):
    def test_elements_and_case(self):
        deck = ("t\nR1 IN out 1k\nC1 out 0 100n\nL1 out 0 1m\n"
                "V1 in 0 DC 5\nI1 0 out 1m\nVBARE n1 0 5\n")
        cards = cards_of(deck)
        self.assertEqual([c["kind"] for c in cards],
                         ["R", "C", "L", "V", "I", "V"])
        r1 = cards[0]
        self.assertEqual(r1["name"], "r1")           # lowercased
        self.assertEqual(r1["nodes"], ["in", "out"])  # lowercased
        self.assertEqual(cards[3]["value"], {"num": 5, "den": 1})  # DC kw
        self.assertEqual(cards[5]["value"], {"num": 5, "den": 1})  # bare
        self.assertEqual(cards[4]["value"], {"num": 1, "den": 1000})

    def test_x_instance(self):
        (x,) = cards_of("t\nX1 in out attn\n")
        self.assertEqual(x, {"kind": "X", "span": {"line": 2, "end_line": 2},
                             "name": "x1", "subckt": "attn",
                             "connections": ["in", "out"]})

    def test_op(self):
        (op,) = cards_of("t\n.op\n")
        self.assertEqual(op, {"kind": "Op", "span": {"line": 2, "end_line": 2}})

    def test_unsupported_cards_are_loud_not_fatal(self):
        deck = ("t\nd1 a 0 dmod\nm1 d g s b nmos\nq1 c b e npn\n"
                "e1 a 0 b 0 2\n.tran 1n 1u\n.model dmod d\n"
                "v2 in 0 pulse (0 5 0 1n 1n 5n 10n)\n"
                "r9 a b 1k tc=1,2\nx9 a b sub p=3\n.op extra\n")
        cards = cards_of(deck)
        self.assertTrue(all(c["kind"] == "Unsupported" for c in cards))
        self.assertEqual([c["spice_kind"] for c in cards],
                         ["D", "M", "Q", "E", ".tran", ".model",
                          "V:form", "R:form", "X:form", "Op:form"])
        self.assertTrue(all(len(c["text"]) <= 200 for c in cards))

    def test_bad_value_is_unsupported(self):
        (c,) = cards_of("t\nr1 a b 1k3\n")
        self.assertEqual(c["spice_kind"], "R:value")


class TestSubckts(unittest.TestCase):
    def test_definition_and_nesting(self):
        deck = ("t\n"
                ".subckt outer a b\n"
                "r1 a b 1k\n"
                ".subckt inner p q\n"
                "r2 p q 2k\n"
                ".ends inner\n"
                "x1 a b inner\n"
                ".ends outer\n"
                "x2 n1 n2 outer\n")
        env = env_of(deck)
        subckts = env["netlist"]["subckts"]
        self.assertEqual(len(subckts), 1)
        outer = subckts[0]
        self.assertEqual(outer["name"], "outer")
        self.assertEqual(outer["ports"], ["a", "b"])
        self.assertEqual(outer["span"], {"line": 2, "end_line": 8})
        kinds = [n["kind"] for n in outer["body"]]
        self.assertEqual(kinds, ["R", "Subckt", "X"])  # nested def stays put
        self.assertEqual(outer["body"][1]["name"], "inner")
        self.assertEqual([c["kind"] for c in env["netlist"]["cards"]], ["X"])

    def test_error_demotion(self):
        # stray .ends / unterminated .subckt / name mismatch / params
        (c,) = cards_of("t\n.ends foo\n")
        self.assertEqual(c["spice_kind"], "Ends:stray")

        env = env_of("t\n.subckt s a\nr1 a 0 1k\n")
        (d,) = env["netlist"]["subckts"]
        self.assertEqual(d["kind"], "Unsupported")
        self.assertEqual(d["spice_kind"], "Subckt:unterminated")

        env = env_of("t\n.subckt s a\nr1 a 0 1k\n.ends other\n")
        (d,) = env["netlist"]["subckts"]
        self.assertEqual(d["spice_kind"], "Subckt:ends-mismatch")

        env = env_of("t\n.subckt s a l=2\nr1 a 0 1k\n.ends s\n")
        (d,) = env["netlist"]["subckts"]
        self.assertEqual(d["spice_kind"], "Subckt:params")


class TestEnvelope(unittest.TestCase):
    def test_envelope_shape_and_key_order(self):
        env = env_of("t\nr1 a b 1k\n")
        self.assertEqual(list(env.keys()),
                         ["schema_version", "language", "frontend",
                          "source_file", "source_sha256", "netlist",
                          "lean_blocks"])
        self.assertEqual(env["schema_version"], "spice-0.1")
        self.assertEqual(env["language"], "spice")
        self.assertEqual(env["lean_blocks"], [])
        self.assertEqual(list(env["netlist"].keys()),
                         ["kind", "title", "subckts", "cards"])
        (r,) = env["netlist"]["cards"]
        self.assertEqual(list(r.keys()),
                         ["kind", "span", "name", "nodes", "value"])

    def test_output_path(self):
        self.assertEqual(extract.output_path("Examples/spice/divider/divider.cir"),
                         "Examples/spice/divider/divider.json")
        self.assertEqual(extract.output_path("foo.sp"), "foo.json")


class TestCommittedExamples(unittest.TestCase):
    EXAMPLES = ["Examples/spice/divider/divider.cir", "Examples/spice/chain/chain.cir",
                "Examples/spice/r2r/r2r.cir"]

    def _has_unsupported(self, node):
        if isinstance(node, dict):
            if node.get("kind") == "Unsupported":
                return True
            return any(self._has_unsupported(v) for v in node.values())
        if isinstance(node, list):
            return any(self._has_unsupported(v) for v in node)
        return False

    def test_deterministic_double_run_and_no_unsupported(self):
        for rel in self.EXAMPLES:
            path = os.path.join(REPO, rel)
            if not os.path.exists(path):
                continue
            with open(path, "rb") as f:
                data = f.read()
            # extract with the repo-relative source_file, as CI does
            a = json.dumps(extract.extract_source(data.decode("utf-8"),
                                                  rel, data), indent=2) + "\n"
            b = json.dumps(extract.extract_source(data.decode("utf-8"),
                                                  rel, data), indent=2) + "\n"
            self.assertEqual(a, b, rel)
            env = json.loads(a)
            self.assertFalse(self._has_unsupported(env), rel)
            out = os.path.join(REPO, extract.output_path(rel))
            if os.path.exists(out):
                with open(out, "r", encoding="ascii") as f:
                    self.assertEqual(f.read(), a,
                                     rel + ": committed .json is stale")


if __name__ == "__main__":
    unittest.main(verbosity=2)
