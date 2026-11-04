"""slang's parse / preprocessor / elaboration ERRORS refuse like its analysis errors do (WP-RB1; Thomas 2026-10-31 and 2026-11-01:
"if slang reports a program illegal, that is a good reason to reject it").

Before this rule an error of the symbolic compilation reached the envelope only when it sat inside a construct the extractor
converts (`InvalidExpression`, `VariableSymbol:type`, ...). A missing `include`, an unknown macro, an unknown package import or
an error in another module of the same sources left an envelope IDENTICAL to the legal program's, and `load_design_sv2` loaded
it (svgolf/design/real-world-sv/rb0/ENVELOPE-ERRORS.md has the four repros and the consumer table). The extractor now carries
every distinct error of `Compilation.getAllDiagnostics()` as `Unsupported` `SlangError:<slang code>` in the top module's
`others`, with the same split as `SlangAnalysis:*`: a top without parameters carries them, a top with parameters and a probe
sidecar has its verdict per POINT (`frontend_errors`), a top with parameters and NO sidecar carries them.

# SYNTHETIC-ORACLE: tests=SlangError | origin=spec | authority=IEEE-1800-2023#3.12,22.4,26.3 | map=diagnostics:slang-getAllDiagnostics;refusals:SlangError-kinds
"""
import json
import tempfile
import unittest
from pathlib import Path

import extract

# name: (the offending line placed in module t, slang's code, a fragment of its message)
REPROS = {
    "missing_include": ('`include "nonexistent.vh"', "CouldNotOpenIncludeFile", "nonexistent.vh"),
    "unknown_macro": ("`NO_SUCH_MACRO", "UnknownDirective", "NO_SUCH_MACRO"),
    "unknown_package": ("import nopkg::*;", "UnknownPackage", "nopkg"),
}
OTHER_MODULE = "module unrelated (input logic b, output logic z);\n  assign z = undeclared_q;\nendmodule\n"


def legal(body="", params="", extra=""):
    return "module t %s(input logic a, output logic y);\n  %s\n  assign y = a;\nendmodule\n%s" % (params, body, extra)


def sv_errors(module):
    return [n for n in module["others"] if n.get("kind") == "Unsupported" and n["sv_kind"].startswith("SlangError:")]


def unsupported(module):
    return [n for n in module["others"] if n.get("kind") == "Unsupported"]


def all_unsupported(node):
    """Every `Unsupported` node anywhere under `node` (a converted construct carries its own, not in `others`)."""
    found = []
    if isinstance(node, dict):
        if node.get("kind") == "Unsupported":
            found.append(node)
        for v in node.values():
            found.extend(all_unsupported(v))
    elif isinstance(node, list):
        for v in node:
            found.extend(all_unsupported(v))
    return found


class SlangErrors(unittest.TestCase):
    COUNTER = 0

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.dir = Path(tmp.name)

    def write(self, source, name=None):
        # a FRESH path per call: pyslang caches source files by path for the whole process, so a second text written to a
        # reused path would be read as the first (svgolf/score/fourstate.py records the same trap)
        SlangErrors.COUNTER += 1
        p = self.dir / (name or "d%d.sv" % SlangErrors.COUNTER)
        p.write_text(source)
        return p

    def envelope(self, source, probed=False):
        src = self.write(source)
        out = Path(str(src) + ".json")
        extract.process_symbolic("t", [str(src)], [], str(out), probed=probed)
        return json.loads(out.read_text())

    def module(self, source, probed=False):
        return self.envelope(source, probed)["design"]["modules"][0]

    def sidecar(self, source, points):
        src = self.write(source)
        out = Path(str(src) + ".json")
        extract.process_symbolic("t", [str(src)], [], str(out), probed=True)
        extract.write_probe_sidecar("t", [str(src)], [], str(out), extract.parse_probe_points(points))
        return json.loads(Path(str(out)[:-5] + ".probes.json").read_text())["points"]

    # --- the four repros -------------------------------------------------------------------------------------------------

    def test_each_silent_shape_is_refused_with_slangs_code_and_message(self):
        cases = {name: (legal(body), code, frag) for name, (body, code, frag) in REPROS.items()}
        cases["error_in_another_module"] = (legal(extra=OTHER_MODULE), "UndeclaredIdentifier", "undeclared_q")
        for name, (source, code, fragment) in cases.items():
            with self.subTest(shape=name):
                module = self.module(source)
                mine = sv_errors(module)
                self.assertEqual([n["sv_kind"] for n in mine], ["SlangError:" + code])
                self.assertIn(fragment, mine[0]["text"])
                self.assertRegex(mine[0]["text"], r"^d\d+\.sv:\d+: ")        # file:line, the basename only
                self.assertEqual(mine[0]["span"]["line"], int(mine[0]["text"].split(":")[1]))
                self.assertGreaterEqual(mine[0]["span"]["line"], 2)
                self.assertEqual(all_unsupported(module), mine)             # and nothing else is loud, anywhere in the module

    def test_the_clean_control_carries_no_marker_and_the_marker_is_the_only_difference(self):
        control = self.envelope(legal())
        self.assertEqual(unsupported(control["design"]["modules"][0]), [])
        want = self.comparable(control)
        for name, source in (("missing_include", legal(REPROS["missing_include"][0])),
                             ("unknown_macro", legal(REPROS["unknown_macro"][0])),
                             ("other_module", legal(extra=OTHER_MODULE))):
            with self.subTest(shape=name):
                env = self.envelope(source)
                m = env["design"]["modules"][0]
                marker = sv_errors(m)
                self.assertEqual(len(marker), 1)
                m["others"] = [n for n in m["others"] if n not in marker]
                self.assertEqual(self.comparable(env), want)

    def comparable(self, env):
        env = json.loads(json.dumps(env))
        env.pop("source_files", None)
        env["design"]["modules"] = env["design"]["modules"][:1]      # the legal top; the extra module of one shape is not its design
        return self.strip_spans(env)

    @staticmethod
    def strip_spans(node):
        if isinstance(node, dict):
            return {k: SlangErrors.strip_spans(v) for k, v in node.items() if k != "span"}
        if isinstance(node, list):
            return [SlangErrors.strip_spans(v) for v in node]
        return node

    def test_an_error_inside_a_converted_construct_is_carried_twice_not_once(self):
        # `InvalidExpression` (the construct) AND `SlangError:UndeclaredIdentifier` (the compilation): the marker never replaces
        m = self.module("module t(input logic a, output logic y);\n  assign y = a & undeclared_q;\nendmodule\n")
        kinds = sorted(n["sv_kind"] for n in all_unsupported(m))
        self.assertIn("SlangError:UndeclaredIdentifier", kinds)
        self.assertTrue(any(k.endswith("InvalidExpression") for k in kinds), kinds)

    def test_analysis_errors_are_not_elaboration_errors(self):
        # two always_comb writers: slang's ANALYSIS pass reports it, `getAllDiagnostics` does not
        m = self.module("module t(input logic a, b, output logic y);\n  always_comb y = a;\n  always_comb y = b;\nendmodule\n")
        self.assertEqual(sv_errors(m), [])
        self.assertEqual([n["sv_kind"] for n in unsupported(m)], ["SlangAnalysis:MultipleAlwaysAssigns"])

    def test_the_operator_markers_stay_and_the_error_is_added(self):
        source = ("module t(input logic [3:0] a, b, output logic [3:0] y, z);\n  assign y = a / b;\n  assign z = undeclared_q;\nendmodule\n")
        kinds = {n["sv_kind"] for n in all_unsupported(self.module(source))}
        self.assertIn("Division:invalid-compilation", kinds)
        self.assertIn("SlangError:UndeclaredIdentifier", kinds)

    def test_a_legal_program_with_a_warning_is_not_refused(self):
        # an unused-variable style warning is not an error: nothing is carried
        self.assertEqual(sv_errors(self.module(legal("logic [3:0] unused_w = 5'b1;"))), [])

    def test_the_marker_is_deterministic(self):
        src = self.write(legal(REPROS["unknown_package"][0]))
        outs = []
        for i in range(2):
            out = Path(str(src) + ".%d.json" % i)
            extract.process_symbolic("t", [str(src)], [], str(out))
            outs.append(out.read_text())
        self.assertEqual(outs[0], outs[1])

    # --- the split with the probe sidecar ---------------------------------------------------------------------------------

    PARAM = "#(parameter int N = 2)"

    def parametric(self, body="", extra=""):
        return ("module t %s(input logic [N-1:0] a, output logic [N-1:0] y);\n  %s\n  assign y = a;\nendmodule\n%s"
                % (self.PARAM, body, extra))

    def test_a_parametric_top_without_a_sidecar_carries_the_marker(self):
        for name, source in (("unknown_package", self.parametric("import nopkg::*;")),
                             ("other_module", self.parametric(extra=OTHER_MODULE))):
            with self.subTest(shape=name):
                self.assertEqual(len(sv_errors(self.module(source, probed=False))), 1)

    def test_a_parametric_top_with_a_sidecar_has_its_verdict_per_point_not_in_the_envelope(self):
        for name, source in (("unknown_package", self.parametric("import nopkg::*;")),
                             ("other_module", self.parametric(extra=OTHER_MODULE))):
            with self.subTest(shape=name):
                self.assertEqual(sv_errors(self.module(source, probed=True)), [])
                self.assertEqual([p["frontend_errors"] for p in self.sidecar(source, "N=1;N=4")], [1, 1])

    def test_a_clean_parametric_top_has_no_errors_at_any_point(self):
        self.assertEqual([p["frontend_errors"] for p in self.sidecar(self.parametric(), "N=1;N=4")], [0, 0])
        self.assertEqual(sv_errors(self.module(self.parametric())), [])

    def test_an_error_only_a_point_override_would_cause_in_another_module_is_not_counted(self):
        # the override applies to the top only (`topModules` + `paramOverrides`): `unrelated` is never at N = 1
        other = ("module unrelated #(parameter int N = 2)(input logic b, output logic z);\n"
                 "  if (N == 1) begin : g\n    $error(\"only illegal at N = 1\");\n  end\n  assign z = b;\nendmodule\n")
        source = self.parametric(extra=other)
        self.assertEqual([p["frontend_errors"] for p in self.sidecar(source, "N=1;N=2")], [0, 0])
        self.assertEqual(sv_errors(self.module(source)), [])

    def test_a_top_with_parameters_whose_default_point_is_the_illegal_one_stays_instantiable_with_a_sidecar(self):
        # illegal at N = 2 only (an elaboration $error), legal at N = 4: with a sidecar the default-point envelope carries no
        # marker, the verdict is the sidecar's per point
        source = ("module t #(parameter int N = 2)(input logic [N-1:0] a, output logic [N-1:0] y);\n"
                  "  if (N == 2) begin : g\n    $error(\"illegal at the default point\");\n  end\n  assign y = a;\nendmodule\n")
        self.assertEqual(sv_errors(self.module(source, probed=True)), [])
        points = {p["overrides"][0]["value"]: p["frontend_errors"] for p in self.sidecar(source, "N=2;N=4")}
        self.assertEqual(points, {2: 1, 4: 0})

    # --- the command line ---------------------------------------------------------------------------------------------------

    def run_main(self, source, extra_args=()):
        src = self.write(source)
        out = Path(str(src) + ".cli.json")
        code = extract.main(["--top", "t", str(src), "-o", str(out)] + list(extra_args))
        self.assertEqual(code, 0)            # the exit status is unchanged: the verdict is in the envelope
        return json.loads(out.read_text())["design"]["modules"][0], out

    def test_cli_marks_without_probe_points_and_leaves_the_envelope_to_the_sidecar_with_them(self):
        source = self.parametric("import nopkg::*;")
        m, _ = self.run_main(source)
        self.assertEqual([n["sv_kind"] for n in sv_errors(m)], ["SlangError:UnknownPackage"])
        m, out = self.run_main(source, ["--probe-points", "N=1;N=4"])
        self.assertEqual(sv_errors(m), [])
        side = json.loads(Path(str(out)[:-5] + ".probes.json").read_text())
        self.assertEqual([p["frontend_errors"] for p in side["points"]], [1, 1])

    def test_cli_parameter_free_top_always_marks(self):
        m, _ = self.run_main(legal(REPROS["missing_include"][0]))
        self.assertEqual([n["sv_kind"] for n in sv_errors(m)], ["SlangError:CouldNotOpenIncludeFile"])

    def test_a_probed_call_does_not_leak_into_the_next_unprobed_call(self):
        source = self.parametric("import nopkg::*;")
        self.run_main(source, ["--probe-points", "N=1"])
        m, _ = self.run_main(source)
        self.assertEqual(len(sv_errors(m)), 1)

    # --- bounds and fail-closed ---------------------------------------------------------------------------------------------

    def test_at_most_twenty_errors_are_listed_and_the_rest_counted(self):
        lines = "\n  ".join("assign q%d = undeclared_%d;" % (i, i) for i in range(25))
        nodes = sv_errors(self.module(legal(lines)))
        self.assertEqual(len(nodes), 21)
        self.assertEqual(nodes[-1]["sv_kind"], "SlangError:more")
        self.assertEqual(nodes[-1]["text"], "5 further slang errors")
        self.assertEqual(len({n["text"] for n in nodes[:-1]}), 20)

    def test_a_diagnostics_list_that_cannot_be_built_fails_closed(self):
        class Boom:
            def getAllDiagnostics(self):
                raise RuntimeError("boom")
        got = extract._slang_error_nodes(Boom(), None)
        self.assertEqual([n["sv_kind"] for n in got], ["SlangError:FrontendFailed"])
        self.assertIn("boom", got[0]["text"])

    # --- the M0 mode is untouched ---------------------------------------------------------------------------------------

    def test_the_m0_single_file_mode_does_not_carry_the_marker(self):
        src = self.write(legal(REPROS["missing_include"][0]), "m0.sv")
        extract.process_file(str(src), "typ")
        self.assertNotIn("SlangError", (self.dir / "m0.sv.json").read_text())


if __name__ == "__main__":
    unittest.main()
