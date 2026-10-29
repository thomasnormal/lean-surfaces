"""Multi-point cross-check probes (`--probe-points`; sv-0.2, 2026-10-28,
round 3 CX).

The symbolic envelope is elaborated by slang at the DEFAULT parameter
point; a probe point re-runs the same extraction with slang's top-level
`paramOverrides` and writes the result to the opt-in sidecar
`<file>.sv.probes.json`, which the Lean side (`LeanModels/Sv/Probe2.lean`)
compares against the envelope instantiated at the same point. These tests
pin the extractor half: the envelope is byte-identical with or without
probes, the sidecar records slang's elaboration AT each point (overrides,
resolved values, frontend errors, the instances of the elaborated
hierarchy), bad points are refused, every committed sidecar regenerates
byte for byte from its recorded `probe_points`, and a disabled fold guard
makes the point extraction differ from the envelope (the mutation the
cross-check exists to catch).
"""
import glob
import json
import os
import tempfile
import unittest
from pathlib import Path

import extract

REPO = Path(__file__).resolve().parents[2]


def params(module):
    return {p["name"]: p.get("resolved") for p in module["params"]
            if p["kind"] == "ParameterDecl"}


def decl(module, name):
    for d in module["decls"] + module.get("ports", []):
        if d.get("name") == name:
            return d
    raise KeyError(name)


class ProbePoints(unittest.TestCase):
    def run_extract(self, source, top, spec, name="fixture"):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        directory = tmp.name
        src = Path(directory) / (name + ".sv")
        src.write_text(source)
        plain = Path(directory) / (name + "_plain.sv.json")
        out = Path(directory) / (name + ".sv.json")
        extract.process_symbolic(top, [str(src)], [], str(plain))
        extract.main(["--top", top, str(src), "-o", str(out), "--probe-points", spec])
        side = Path(directory) / (name + ".sv.probes.json")
        return plain.read_bytes(), out.read_bytes(), json.loads(side.read_text())

    ADDER = ("module top #(parameter int N = 4, parameter int W = N + 1) "
             "(input logic [N-1:0] a, output logic [W-1:0] y); "
             "assign y = a + 1'b1; endmodule\n")

    def test_envelope_unchanged_and_points_recorded(self):
        plain, out, side = self.run_extract(self.ADDER, "top", "N=2;N=8,W=3")
        self.assertEqual(plain, out)
        self.assertEqual(side["schema_version"], extract.PROBE_SCHEMA_VERSION)
        self.assertEqual(side["top"], "top")
        self.assertEqual(side["probe_points"], "N=2;N=8,W=3")
        self.assertEqual([p["overrides"] for p in side["points"]],
                         [[{"name": "N", "value": 2}],
                          [{"name": "N", "value": 8}, {"name": "W", "value": 3}]])
        # slang elaborated each point: W = N + 1 follows N where not given.
        self.assertEqual(params(side["points"][0]["module"]), {"N": 2, "W": 3})
        self.assertEqual(params(side["points"][1]["module"]), {"N": 8, "W": 3})
        self.assertEqual(decl(side["points"][1]["module"], "y")["width"]["resolved"], 3)
        self.assertTrue(all(p["frontend_errors"] == 0 for p in side["points"]))
        self.assertNotIn('"span"', json.dumps(side["points"]))

    def test_points_are_sorted_into_declaration_order(self):
        _, _, side = self.run_extract(self.ADDER, "top", "W=3,N=8")
        self.assertEqual(side["probe_points"], "N=8,W=3")

    def test_bad_points_are_refused(self):
        for spec in ("N", "N=x", "N=1,N=2", ";", "1N=2"):
            with self.subTest(spec=spec):
                with self.assertRaises(extract.ExtractError):
                    extract.parse_probe_points(spec)
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "x.sv"
            src.write_text(self.ADDER)
            out = Path(directory) / "x.sv.json"
            # Not a parameter of the top: refused, no sidecar written.
            self.assertEqual(extract.main(["--top", "top", str(src), "-o", str(out),
                                           "--probe-points", "Q=1"]), 1)
            self.assertFalse((Path(directory) / "x.sv.probes.json").exists())

    def test_probe_points_need_symbolic_mode(self):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "x.sv"
            src.write_text(self.ADDER)
            self.assertEqual(extract.main([str(src), "--probe-points", "N=1"]), 1)

    def test_frontend_errors_at_a_point_are_counted(self):
        source = ("module top #(parameter int N = 4) (input logic [3:0] a, "
                  "output logic [3:0] y); assign y = {N{1'b1}} & a; endmodule\n")
        _, _, side = self.run_extract(source, "top", "N=4;N=0")
        self.assertEqual(side["points"][0]["frontend_errors"], 0)
        self.assertGreater(side["points"][1]["frontend_errors"], 0)

    def test_instances_carry_their_point(self):
        source = ("module child #(parameter int W = 2) (input logic [W-1:0] x, "
                  "output logic [W-1:0] y); assign y = ~x; endmodule\n"
                  "module top #(parameter int N = 3) (input logic [N-1:0] a, "
                  "output logic [N-1:0] y, output logic [1:0] z); "
                  "child #(.W(N)) c1 (.x(a), .y(y)); "
                  "child c2 (.x(a[1:0]), .y(z)); endmodule\n")
        _, _, side = self.run_extract(source, "top", "N=5")
        insts = side["points"][0]["instances"]
        self.assertEqual([(i["module"], i["overrides"]) for i in insts],
                         [("child", [{"name": "W", "value": 5}]), ("child", [])])
        self.assertEqual(params(insts[0]["design"]), {"W": 5})
        self.assertEqual(params(insts[1]["design"]), {"W": 2})

    def test_unrelated_top_neither_receives_the_point_nor_counts(self):
        # Round 3 CX repair (verifier repro `multi_top`): slang applies
        # `paramOverrides` to EVERY top-level module, so an uninstantiated
        # module of the same sources with a parameter `N` that fails at
        # N = 8 made the DUT's point look rejected. The probe compilation
        # elaborates `--top` alone, like a testbench's `#(.N(8))`.
        source = ("module multi_top #(parameter int N = 4) (input logic [N-1:0] a, "
                  "output logic [N-1:0] y); assign y = ~a; endmodule\n"
                  "module side_mod #(parameter int N = 4) (input logic [3:0] b, "
                  "output logic [3:0] z); if (N > 6) begin : bad "
                  "$error(\"side_mod: N too large\"); end assign z = b; endmodule\n")
        plain, out, side = self.run_extract(source, "multi_top", "N=4;N=8")
        self.assertEqual(plain, out)
        self.assertEqual([p["frontend_errors"] for p in side["points"]], [0, 0])
        self.assertEqual(params(side["points"][1]["module"]), {"N": 8})
        self.assertEqual(side["points"][1]["module"]["others"], [])

    def test_untyped_sized_child_override_is_unprobed(self):
        # Round 3 CX repair (verifier repro `hier_untyped2`): an UNTYPED
        # parameter takes the type of its final value (§6.20.2), so
        # `#(.P(4'd9))` gives a 4-bit `P` that an integer probe `P=9`
        # (32-bit signed) does not reproduce — recorded unprobed (null,
        # loud on the Lean side), not merged with the int instance.
        source = ("module uchild2 #(parameter P = 3'd5) (input logic [3:0] x, "
                  "output logic [7:0] b); assign b = $bits(P) + x; endmodule\n"
                  "module top #(parameter int N = 1) (input logic [3:0] a, "
                  "output logic [7:0] b, b2); "
                  "uchild2 #(.P(4'd9)) u (.x(a), .b(b)); "
                  "uchild2 #(.P(9)) v (.x(a), .b(b2)); endmodule\n")
        _, _, side = self.run_extract(source, "top", "N=2")
        insts = side["points"][0]["instances"]
        self.assertEqual([(i["module"], i["overrides"]) for i in insts],
                         [("uchild2", None),
                          ("uchild2", [{"name": "P", "value": 9}])])
        self.assertIsNone(insts[0]["design"])
        # A declared range keeps the instance's type at an integer probe.
        typed = ("module c #(parameter [3:0] Q = 2, parameter int S = 4) "
                 "(output logic [3:0] y); assign y = Q + S; endmodule\n"
                 "module top #(parameter int N = 1) (output logic [3:0] y); "
                 "c #(.Q(4'd3), .S(4'd2)) u (.y(y)); endmodule\n")
        _, _, side = self.run_extract(typed, "top", "N=2")
        self.assertEqual(side["points"][0]["instances"][0]["overrides"],
                         [{"name": "Q", "value": 3}, {"name": "S", "value": 2}])

    def test_disabled_fold_guard_is_visible_at_the_point(self):
        # The round-2 cell-index guard, disabled: the envelope freezes
        # `m[K]` to the default cell `m[0]`, the extraction at K = 2 says
        # `m[2]` — exactly the difference `PDesign.pointVerdict` reports.
        source = ("module top #(parameter int K = 0) (input logic a, "
                  "output logic [3:0] y); logic m [4]; assign m[K] = a; "
                  "assign y = {m[3], m[2], m[1], m[0]}; endmodule\n")
        saved = extract._sym_cell_index_point_dependent
        extract._sym_cell_index_point_dependent = lambda *a, **k: False
        try:
            _, out, side = self.run_extract(source, "top", "K=2")
        finally:
            extract._sym_cell_index_point_dependent = saved
        envelope = json.loads(out)

        def target(module):
            return module["processes"][0]["target"]["name"]

        self.assertEqual(target(envelope["design"]["modules"][0]), "m[0]")
        self.assertEqual(target(side["points"][0]["module"]), "m[2]")

    def test_committed_sidecars_regenerate(self):
        sidecars = sorted(glob.glob(str(REPO / "Examples" / "system-verilog" / "**"
                                        / "*.sv.probes.json"), recursive=True))
        self.assertTrue(sidecars)
        for path in sidecars:
            with self.subTest(sidecar=os.path.relpath(path, REPO)):
                side = json.loads(Path(path).read_text())
                srcs = [str(REPO / s["path"]) for s in side["source_files"]]
                with tempfile.TemporaryDirectory() as directory:
                    out = Path(directory) / Path(path).name.replace(".probes.json", ".json")
                    cwd = os.getcwd()
                    os.chdir(REPO)
                    try:
                        extract.main(["--top", side["top"],
                                      *[os.path.relpath(s, REPO) for s in srcs],
                                      "-o", str(out), "--probe-points", side["probe_points"]])
                    finally:
                        os.chdir(cwd)
                    env = Path(path[:-len(".probes.json")] + ".json")
                    self.assertEqual(out.read_bytes(), env.read_bytes())
                    regen = Path(directory) / Path(path).name
                    self.assertEqual(regen.read_bytes(), Path(path).read_bytes())


if __name__ == "__main__":
    unittest.main()
