"""slang's ANALYSIS errors refuse like its elaboration errors do (Thomas 2026-11-01).

"slang reports a program illegal" means the FULL slang driver: parse, elaboration AND analysis errors.
`Compilation.getAllDiagnostics()` does not contain the diagnostics of the analysis pass that the `slang` driver
runs after elaboration (`Driver.runAnalysis`, `pyslang.analysis.AnalysisManager`): `MultipleAlwaysAssigns`,
`MixedVarAssigns`, `MultipleContAssigns` (all three WARNINGS by slang's own definition that the driver promotes to
errors, so a bare `isError()` misses them), `InputPortAssign` and `AlwaysWithoutTimingControl`. The extractor asks the
driver's own severities (`_slang_driver`) and refuses with the stable kind `SlangAnalysis:<slang code name>` and slang's
message; the verdict of a top with parameters is per POINT (the probe sidecar's `frontend_errors`), because an analysis
error can depend on the point and the default-point envelope must stay instantiable at a legal one.

# SYNTHETIC-ORACLE: tests=SlangAnalysis | origin=spec | authority=IEEE-1800-2023#9.2.2.2,6.5,23.3.3.2,9.2.2.1 | map=driver:slang-analysis-pass;refusals:SlangAnalysis-kinds
"""
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

import extract

REPO = Path(__file__).resolve().parents[2]

SHAPES = {
    # name: (module body, slang code, a fragment of slang's message)
    "two_always": ("always_comb y = a;\n  always_comb y = b;",
                   "MultipleAlwaysAssigns", "cannot be written to by any other process"),
    "mixed": ("assign y = a;\n  always_comb y = b;",
              "MixedVarAssigns", "cannot mix continuous and procedural assignments"),
    "input": ("assign a = b;\n  assign y = a;",
              "InputPortAssign", "cannot assign to input port 'a'"),
    "initial_comb": ("initial y = 1'b0;\n  always_comb y = a;",
                     "MultipleAlwaysAssigns", "cannot be written to by any other process"),
    "always_notime": ("always y = a;",
                      "AlwaysWithoutTimingControl", "does not advance time"),
    "two_assign": ("assign y = a;\n  assign y = b;",
                   "MultipleContAssigns", "cannot have multiple continuous assignments"),
}


def design(body, params="", extra=""):
    return (extra + "module top " + params + "(input logic a, b, output logic y);\n  " + body + "\nendmodule\n")


def kinds(module):
    return [n for n in module["others"] if n.get("kind") == "Unsupported"]


class SlangAnalysisErrors(unittest.TestCase):
    def envelope(self, source, top="top"):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        src, out = Path(tmp.name) / "d.sv", Path(tmp.name) / "d.sv.json"
        src.write_text(source)
        extract.process_symbolic(top, [str(src)], [], str(out))
        return json.loads(out.read_text())["design"]["modules"][0]

    def test_each_analysis_shape_is_refused_with_slangs_own_message(self):
        for name, (body, code, fragment) in SHAPES.items():
            with self.subTest(shape=name):
                mine = [n for n in kinds(self.envelope(design(body)))
                        if n["sv_kind"].startswith("SlangAnalysis:")]
                self.assertEqual([n["sv_kind"] for n in mine], ["SlangAnalysis:" + code])
                self.assertIn(fragment, mine[0]["text"])
                self.assertGreaterEqual(mine[0]["span"]["line"], 2)

    def test_getalldiagnostics_alone_is_silent_on_these_shapes(self):
        # the reason for the rule: nothing in the elaboration diagnostics shows them
        from pyslang.ast import Compilation
        from pyslang.syntax import SyntaxTree
        for name, (body, code, _) in SHAPES.items():
            if code == "AlwaysWithoutTimingControl":
                continue            # slang itself counts this one as a raw error once analysed
            with self.subTest(shape=name):
                comp = Compilation()
                comp.addSyntaxTree(SyntaxTree.fromText(design(body)))
                self.assertEqual([d for d in comp.getAllDiagnostics() if d.isError()], [])

    def test_driver_promoted_warnings_are_errors_for_the_extractor(self):
        # MultipleAlwaysAssigns, MixedVarAssigns, MultipleContAssigns are warnings in a bare DiagnosticEngine
        # and errors in the slang driver; pins the pinned pyslang's severity table
        import pyslang
        engine = extract._slang_driver().diagEngine
        for name in ("MultipleAlwaysAssigns", "MixedVarAssigns", "MultipleContAssigns",
                     "InputPortAssign", "AlwaysWithoutTimingControl"):
            with self.subTest(code=name):
                self.assertEqual(engine.getSeverity(getattr(pyslang.Diags, name), pyslang.SourceLocation()),
                                 pyslang.DiagnosticSeverity.Error)

    def test_clean_designs_carry_no_analysis_marker(self):
        for body in ("assign y = a & b;", "always_comb y = a | b;",
                     "always_comb begin y = a; y = b; end"):
            with self.subTest(body=body):
                self.assertEqual(kinds(self.envelope(design(body))), [])

    def test_a_program_pragma_cannot_downgrade_the_report(self):
        # the slang driver itself ACCEPTS this program (the pragma ignores the warning that the driver promotes);
        # the extractor reads the severity with no source location, so it refuses (the svGolf source gate refuses
        # pragma comments anyway, `sg-pragma-dir`; this does not rely on it)
        source = design('`pragma diagnostic push\n`pragma diagnostic ignore="-Wmultiple-always-assigns"\n'
                        '  always_comb y = a;\n  always_comb y = b;\n`pragma diagnostic pop')
        self.assertEqual([n["sv_kind"] for n in kinds(self.envelope(source))],
                         ["SlangAnalysis:MultipleAlwaysAssigns"])

    def test_a_module_the_top_does_not_instantiate_is_not_analysed(self):
        source = design("assign y = a & b;",
                        extra="module side(input logic a, output logic y);\n  always_comb y = a;\n"
                              "  always_comb y = ~a;\nendmodule\n")
        self.assertEqual(kinds(self.envelope(source)), [])

    def test_an_instantiated_child_is_analysed(self):
        source = design("child u(.a(a), .y(y));",
                        extra="module child(input logic a, output logic y);\n  always_comb y = a;\n"
                              "  always_comb y = ~a;\nendmodule\n")
        got = [n["sv_kind"] for n in kinds(self.envelope(source))]
        self.assertIn("SlangAnalysis:MultipleAlwaysAssigns", got)

    def test_a_top_with_parameters_gets_a_verdict_per_point(self):
        # at N = 4 the blocks write y[0] and y[1] (legal), at N = 2 both write y[0]
        source = ("module top #(parameter int N = 4)(input logic [1:0] a, output logic [1:0] y);\n"
                  "  always_comb y[0] = a[0];\n  always_comb y[N/4] = a[1];\nendmodule\n")
        # the DEFAULT envelope (N = 4, legal) is unchanged by the rule, and a default-point error of a top with
        # parameters does not enter the envelope either: the envelope must stay instantiable at the legal point
        self.assertEqual(kinds(self.envelope(source)), [])
        illegal_default = source.replace("N = 4", "N = 2")
        self.assertEqual(kinds(self.envelope(illegal_default)), [])
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        src, out = Path(tmp.name) / "d.sv", Path(tmp.name) / "d.sv.json"
        src.write_text(source)
        extract.process_symbolic("top", [str(src)], [], str(out))
        extract.write_probe_sidecar("top", [str(src)], [], str(out),
                                    extract.parse_probe_points("N=4;N=2"))
        points = {pt["overrides"][0]["value"]: pt for pt in
                  json.loads(Path(str(out)[:-5] + ".probes.json").read_text())["points"]}
        self.assertEqual(points[4]["frontend_errors"], 0)
        self.assertNotIn("frontend_analysis", points[4])
        self.assertEqual(points[2]["frontend_errors"], 1)
        self.assertEqual([a["code"] for a in points[2]["frontend_analysis"]], ["MultipleAlwaysAssigns"])
        self.assertIn("cannot be written to by any other process", points[2]["frontend_analysis"][0]["message"])

    def test_the_analysis_that_cannot_run_fails_closed(self):
        class Boom:
            @property
            def sourceManager(self):
                raise RuntimeError("boom")
        got = extract._slang_analysis_errors(Boom(), "top")
        self.assertEqual([g[0] for g in got], ["AnalysisFailed"])

    def test_svgolf_classifies_the_same_diagnostics(self):
        path = REPO / "svgolf" / "score" / "slangdriver.py"
        if not path.exists():
            self.skipTest("svgolf/ is not part of this checkout")
        spec = importlib.util.spec_from_file_location("svgolf_slangdriver", path)
        sg = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(sg)
        import pyslang
        from pyslang.syntax import SyntaxTree
        for name, (body, _, _) in SHAPES.items():
            with self.subTest(shape=name):
                sm = pyslang.SourceManager()
                tree = SyntaxTree.fromText(design(body), sm, "d.sv")
                mine = [(c, m) for c, m, _, _ in extract._slang_analysis_errors(tree, "top")]
                theirs = [(c, m) for c, m, _, _ in sg.analysis_errors([tree], "top")]
                self.assertEqual(mine, theirs)
                self.assertTrue(mine)


if __name__ == "__main__":
    unittest.main()
