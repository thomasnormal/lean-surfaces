"""Module instances in sv-0.2 symbolic mode (F3, 2026-10-28).

A module instance is ONE `Instance` node (definition name, lexical generate
path, symbolic parameter overrides, one `PortConn` per child port in the
child's port order) inside `generates` (module level) or a generate body;
every definition the top instantiates, transitively, follows the top in
`design.modules`, elaborated alone at its own defaults. Designs without
instances are byte-identical to before (one module, `others: []`).
"""
import json
import tempfile
import unittest
from pathlib import Path

import extract


def strip(node):
    if isinstance(node, dict):
        return {key: strip(value) for key, value in node.items()
                if key not in ("span", "resolved_width", "width")}
    if isinstance(node, list):
        return [strip(value) for value in node]
    return node


def find_kind(node, kind, found=None):
    found = [] if found is None else found
    if isinstance(node, dict):
        if node.get("kind") == kind:
            found.append(node)
        for value in node.values():
            find_kind(value, kind, found)
    elif isinstance(node, list):
        for value in node:
            find_kind(value, kind, found)
    return found


def sv_kinds(node):
    return [n.get("sv_kind") for n in find_kind(node, "Unsupported")]


class SymbolicInstances(unittest.TestCase):
    def extract(self, source, top="top"):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic(top, [str(src)], [], str(out))
            return json.loads(out.read_text())

    def test_generate_loop_instance(self):
        env = self.extract("""
module fa (input logic a, b, ci, output logic s, co);
  assign s = a ^ b ^ ci;
  assign co = (a & b) | (ci & (a ^ b));
endmodule
module top #(parameter int N = 4) (input logic [N-1:0] a, b, output logic [N-1:0] s);
  logic [N:0] c;
  assign c[0] = 1'b0;
  for (genvar i = 0; i < N; i++) begin : g_bit
    fa u (.a(a[i]), .b(b[i]), .ci(c[i]), .s(s[i]), .co(c[i+1]));
  end
endmodule
""")
        modules = env["design"]["modules"]
        self.assertEqual([m["name"] for m in modules], ["top", "fa"])
        self.assertEqual(env["design"]["others"], [])
        loop = modules[0]["generates"][0]
        self.assertEqual(loop["kind"], "GenerateFor")
        inst = strip(loop["body"][0])
        self.assertEqual(inst["kind"], "Instance")
        self.assertEqual((inst["name"], inst["module"]), ("u", "fa"))
        self.assertEqual(inst["path"], [{"label": "g_bit", "genvar": "i"}])
        self.assertEqual(inst["params"], [])
        self.assertEqual([(p["port"], p["dir"]) for p in inst["ports"]],
                         [("a", "in"), ("b", "in"), ("ci", "in"), ("s", "out"), ("co", "out")])
        self.assertEqual(inst["ports"][0]["expr"]["kind"], "BitSel")
        self.assertEqual(inst["ports"][0]["expr"]["index"], {"kind": "GenvarRef", "name": "i"})
        self.assertEqual(inst["ports"][4]["target"]["index"]["kind"], "Binary")
        self.assertEqual(sv_kinds(env), [])
        # The definition is the module `--top fa` would emit.
        alone = self.extract("""
module fa (input logic a, b, ci, output logic s, co);
  assign s = a ^ b ^ ci;
  assign co = (a & b) | (ci & (a ^ b));
endmodule
""", top="fa")
        self.assertEqual(strip(modules[1]), strip(alone["design"]["modules"][0]))

    def test_overrides_named_ordered_and_defaults(self):
        env = self.extract("""
module child #(parameter int W = 2, parameter int K = W + 1) (
  input logic [W-1:0] x, input logic en, output logic [K-1:0] y);
  assign y = en ? {x, 1'b1} : '0;
endmodule
module top #(parameter int N = 3) (input logic [N-1:0] a, input logic e,
    output logic [N:0] o1, output logic [7:0] o2, output logic [3:0] o3);
  child #(.W(N)) c1 (.x(a), .en(e), .y(o1));
  child #(N + 2, 9) c2 (a, e & a[0], o2);
  child c3 (.x(a[1:0] ^ 2'b11), .en(), .y(o3[2:0]));
endmodule
""")
        insts = [strip(g) for g in env["design"]["modules"][0]["generates"]]
        self.assertEqual([i["name"] for i in insts], ["c1", "c2", "c3"])
        self.assertEqual(insts[0]["params"], [{"name": "W", "expr": {"kind": "ParamRef", "name": "N"}}])
        self.assertEqual([p["name"] for p in insts[1]["params"]], ["W", "K"])
        self.assertEqual(insts[1]["params"][0]["expr"]["kind"], "Binary")
        self.assertEqual(insts[2]["params"], [])
        # Ordered connections resolve to the child's port names.
        self.assertEqual([p["port"] for p in insts[1]["ports"]], ["x", "en", "y"])
        self.assertEqual(insts[1]["ports"][1]["expr"]["kind"], "Binary")
        # An unconnected input net, an output into a part select.
        self.assertEqual(insts[2]["ports"][1], {"kind": "PortConn", "port": "en", "dir": "in",
                                                "expr": None, "net": True})
        self.assertEqual(insts[2]["ports"][2]["target"]["kind"], "PartSel")
        # One definition for three instances at three parameter points.
        self.assertEqual([m["name"] for m in env["design"]["modules"]], ["top", "child"])

    def test_unconnected_var_input_and_port_default(self):
        env = self.extract("""
module ch (input logic a, input var logic b, output logic [1:0] y);
  assign y = {a, b};
endmodule
module top (output logic [1:0] y);
  ch u (.a(), .b(), .y(y));
endmodule
""")
        ports = strip(env["design"]["modules"][0]["generates"][0])["ports"]
        self.assertEqual([(p["port"], p.get("net")) for p in ports[:2]], [("a", True), ("b", False)])
        env = self.extract("""
module ch (input logic a = 1'b1, output logic y);
  assign y = a;
endmodule
module top (output logic y);
  ch u (.y(y));
endmodule
""")
        self.assertIn("PortConnection:default", sv_kinds(env))

    def test_nested_hierarchy_and_paths(self):
        env = self.extract("""
module leaf (input logic a, output logic y);
  assign y = ~a;
endmodule
module mid (input logic [1:0] a, output logic [1:0] y);
  leaf l0 (.a(a[0]), .y(y[0]));
  leaf l1 (.a(a[1]), .y(y[1]));
endmodule
module top #(parameter int N = 2, parameter bit E = 1) (
    input logic [1:0] a, output logic [1:0] y, output logic [N-1:0] z, output logic q);
  mid m (.*);
  for (genvar i = 0; i < N; i++) begin : g_o
    for (genvar j = 0; j < 1; j++) begin
      leaf u (.a(a[0]), .y(z[i]));
    end
  end
  if (E) begin : g_e
    leaf v (.a(a[1]), .y(q));
  end
endmodule
""")
        self.assertEqual([m["name"] for m in env["design"]["modules"]], ["top", "mid", "leaf"])
        insts = find_kind(env["design"]["modules"][0], "Instance")
        paths = {i["name"]: i["path"] for i in insts}
        self.assertEqual(paths["m"], [])
        self.assertEqual(paths["u"], [{"label": "g_o", "genvar": "i"},
                                      {"label": "genblk1", "genvar": "j"}])
        self.assertEqual(paths["v"], [{"label": "g_e", "genvar": None}])
        # `.*` connects by name.
        m = [i for i in insts if i["name"] == "m"][0]
        self.assertEqual([p["expr" if p["dir"] == "in" else "target"]["name"] for p in m["ports"]],
                         ["a", "y"])

    def test_untaken_branch_and_inout_are_loud(self):
        env = self.extract("""
module leaf (input logic a, output logic y);
  assign y = a;
endmodule
module top #(parameter bit E = 1) (input logic a, output logic q);
  if (E) begin : g_t
    leaf v (.a(a), .y(q));
  end else begin : g_f
    leaf w (.a(~a), .y(q));
  end
endmodule
""")
        self.assertIn("UninstantiatedDefSymbol:UninstantiatedDef", sv_kinds(env))
        env = self.extract("""
module io (inout wire p, output logic y);
  assign y = p;
endmodule
module top (inout wire p, output logic y);
  io u (.p(p), .y(y));
endmodule
""")
        self.assertIn("PortConnection:InOut", sv_kinds(env["design"]["modules"][0]))

    def test_integer_actuals_are_emitted_unconverted(self):
        # slang binds an input actual converted to the port type of the
        # instance it bound (defaults / FIRST generate iteration); an
        # integer constant under that conversion used to be folded into a
        # literal of THAT width (`.i(5)` into the 1-bit port of `W = 1`).
        # The INT-class tree is emitted instead (Lean fits it per point);
        # its context-WIDENED binding (a port wider than 32 bits) is loud.
        env = self.extract("""
module pc #(parameter int W = 1) (input logic [W-1:0] i, output logic [W-1:0] o);
  assign o = i;
endmodule
module top #(parameter int N = 4) (output logic [5:0] g6, f6, output logic [N+1:0] o1,
                                   output logic [N-1:0] o2, output logic [39:0] o40,
                                   output logic [N-1:0] o3);
  for (genvar g = 1; g <= 3; g++) begin : gl
    pc #(.W(g)) pg (.i(g), .o(g6[(g*(g-1))/2 +: g]));
    pc #(.W(g)) pf (.i(5), .o(f6[(g*(g-1))/2 +: g]));
  end
  pc #(.W(N+2)) c1 (.i(-1), .o(o1));
  pc #(.W(N)) c2 (.i(N*3-1), .o(o2));
  pc #(.W(40)) c3 (.i(-1), .o(o40));
  pc #(.W(N)) c4 (.i(4'd9), .o(o3));
endmodule
""")
        insts = {i["name"]: i for i in find_kind(env["design"]["modules"][0], "Instance")}

        def actual(name):
            return strip(insts[name]["ports"][0]["expr"])
        self.assertEqual(actual("pg"), {"kind": "GenvarRef", "name": "g"})
        self.assertEqual(actual("pf"), {"kind": "Int", "value": 5})
        self.assertEqual(actual("c1"), {"kind": "Unary", "op": "-",
                                        "operand": {"kind": "Int", "value": 1}})
        self.assertEqual(actual("c2")["kind"], "Binary")
        self.assertEqual(actual("c2")["left"]["left"], {"kind": "ParamRef", "name": "N"})
        self.assertEqual(actual("c3")["sv_kind"], "PortConnection:int-width")
        # A SIZED literal keeps the ordinary conversion (a context-width Resize).
        self.assertEqual(actual("c4")["kind"], "Literal")

    def test_instance_free_design_is_one_module(self):
        env = self.extract("""
module top (input logic a, output logic y);
  assign y = ~a;
endmodule
""")
        self.assertEqual(len(env["design"]["modules"]), 1)
        self.assertEqual(env["design"]["others"], [])


if __name__ == "__main__":
    unittest.main()
