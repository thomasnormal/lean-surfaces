"""Structural admission tests; simulation expectations live in reference fixtures."""

import unittest
from pathlib import Path

import extract
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree


REPO = Path(__file__).resolve().parents[2]


def lower(source, require_valid=False):
    extract._SYM = None
    extract._SOURCE_BYTES = source.encode()
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    if require_valid and any(diagnostic.isError() for diagnostic in compilation.getAllDiagnostics()):
        raise AssertionError("regression source has frontend errors")
    return extract.convert_design(tree.sourceManager, compilation)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def case_source(body):
    return "module top; logic [3:0] subject; initial begin " + body + " end endmodule"


class OrdinaryCases(unittest.TestCase):
    def assert_refused(self, body, tag):
        kinds = [node.get("sv_kind") for node in nodes(lower(case_source(body)))]
        self.assertIn(tag, kinds)

    def test_reference_fixtures_are_admitted(self):
        sources = sorted((REPO / "harness/sv/ordinary_cases").glob("*.sv"))
        self.assertEqual(len(sources), 6)
        for source in sources:
            with self.subTest(source=source.name):
                design = lower(source.read_text())
                self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))
                self.assertTrue(any(node.get("case_lowered") for node in nodes(design)))

    def test_whole_case_bound_width(self):
        design = lower(case_source("case(subject) 4'd1:; 32'd2:; endcase"))
        comparisons = [node["cond"] for node in nodes(design) if node.get("case_lowered")]
        self.assertEqual(len(comparisons), 2)
        for comparison in comparisons:
            self.assertEqual(comparison["op"], "===")
            self.assertEqual(comparison["left"]["width"], 32)
            self.assertEqual(comparison["right"]["width"], 32)

    def test_subject_side_effects_stay_loud(self):
        self.assert_refused("case(subject++) 4'd1:; endcase", "CaseStatement:subject")

    def test_pattern_side_effects_stay_loud(self):
        self.assert_refused("case(subject) subject++:; endcase", "CaseStatement:pattern")

    def test_folded_calls_stay_loud(self):
        function = ('function automatic logic [3:0] bump(); '
                    '$display("CALLED"); bump = 1; endfunction ')
        expressions = ("bump()", "bump() + 4'd0", "1 ? bump() : 4'd0",
                       "{bump()}", "~bump()", "4'(bump())")
        for position in ("subject", "pattern"):
            for expression in expressions:
                with self.subTest(position=position, expression=expression):
                    subject = expression if position == "subject" else "subject"
                    pattern = expression if position == "pattern" else "4'd1"
                    body = "case(" + subject + ") " + pattern + ":; 32'd2:; endcase"
                    source = case_source(body).replace("initial begin", function + "initial begin")
                    kinds = [node.get("sv_kind") for node in nodes(lower(source, require_valid=True))]
                    self.assertIn("CaseStatement:" + position, kinds)

    def test_nested_increment_stays_loud(self):
        self.assert_refused("case(subject++ + 4'd0) 4'd1:; 32'd2:; endcase",
                            "CaseStatement:subject")
        self.assert_refused("case(subject) subject++ + 4'd0:; 32'd2:; endcase",
                            "CaseStatement:pattern")

    def test_qualifiers_stay_loud(self):
        for qualifier in ("unique", "unique0", "priority"):
            with self.subTest(qualifier=qualifier):
                self.assert_refused(qualifier + " case(subject) 4'd1:; endcase",
                                    "CaseStatement:" + qualifier.capitalize())

    def test_inside_stays_loud(self):
        self.assert_refused("case(subject) inside 4'd1:; endcase", "CaseStatement:Inside")

    def test_nonintegral_subject_stays_loud(self):
        self.assert_refused("case(1.5) 1.5:; endcase", "CaseStatement:subject")

    def test_default_only_stays_loud(self):
        self.assert_refused("case(subject) default:; endcase", "CaseStatement:empty")

    def test_frontend_error_does_not_disappear(self):
        source = case_source("case(subject) 4'd1:; endcase")
        source += " module invalid; initial undeclared = 1; endmodule"
        kinds = [node.get("sv_kind") for node in nodes(lower(source))]
        self.assertIn("CaseStatement:invalid-compilation", kinds)


if __name__ == "__main__":
    unittest.main()
