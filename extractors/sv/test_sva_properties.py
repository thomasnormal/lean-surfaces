"""Concurrent SVA members stay in the symbolic property envelope (F1)."""
import json
import tempfile
import unittest
from pathlib import Path

import extract


class SvaProperties(unittest.TestCase):
    def test_assert_assume_cover_are_retained_metadata(self):
        source = """module top(input logic clk, rst_n, a, b, output logic q);
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) q <= 1'b0; else q <= a;
  assert property (@(posedge clk) disable iff (!rst_n) a |-> b);
  assume property (@(posedge clk) a |=> b);
  cover property (@(posedge clk) a ##1 b);
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            module = json.loads(out.read_text())["design"]["modules"][0]
        self.assertEqual([p["property_kind"] for p in module["properties"]],
                         ["assert", "assume", "cover"])
        self.assertEqual([p["clock"] for p in module["properties"]],
                         ["clk", "clk", "clk"])
        self.assertEqual([p["kind"] for p in module["properties"]],
                         ["SvaProperty"] * 3)
        self.assertEqual(module["properties"][0]["ast"]["kind"], "SvaCheck")
        self.assertEqual(module["properties"][0]["ast"]["edge"], "posedge")
        self.assertEqual(module["properties"][0]["ast"]["property"]["kind"],
                         "SvaDisable")
        self.assertEqual(module["properties"][1]["ast"]["property"]["kind"],
                         "SvaNonoverlap")
        self.assertEqual(module["properties"][2]["ast"]["property"]["kind"],
                         "SvaAlways")
        self.assertEqual([p["kind"] for p in module["processes"]],
                         ["AlwaysPosedge"])
        self.assertFalse(any(n.get("sv_kind") == "ProceduralBlockSymbol:NoEventControl"
                             for n in module["others"]))

    def test_negedge_and_nonoverlap_are_structured(self):
        source = """module top(input logic clk, req, ack);
  assert property (@(negedge clk) req |=> ack);
  cover property (@(negedge clk) req ##1 ack);
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "negedge.sv"
            out = Path(directory) / "negedge.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            properties = json.loads(out.read_text())["design"]["modules"][0]["properties"]
        self.assertEqual([p["ast"]["edge"] for p in properties],
                         ["negedge", "negedge"])
        self.assertEqual(properties[0]["ast"]["property"]["kind"],
                         "SvaNonoverlap")
        self.assertEqual(properties[1]["ast"]["property"]["body"]["kind"],
                         "SvaConcat")

    def test_generate_scope_assertion_is_retained_at_module_level(self):
        source = """module top(input logic clk, a);
  if (1) begin : g
    assert property (@(posedge clk) a);
  end
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "generated.sv"
            out = Path(directory) / "generated.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            module = json.loads(out.read_text())["design"]["modules"][0]
        self.assertEqual(len(module["properties"]), 1)
        self.assertEqual(module["properties"][0]["property_kind"], "assert")
        self.assertEqual(module["properties"][0]["path"], ["g"])
        self.assertEqual(module["generates"][0]["then"], [])

    def test_structured_boolean_ast_keeps_slang_expression_tree(self):
        source = """module top(input logic clk, a, b, c);
  assert property (@(posedge clk) (a && b) |-> (!c || (a === b)));
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "expr.sv"
            out = Path(directory) / "expr.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            prop = json.loads(out.read_text())["design"]["modules"][0]["properties"][0]
        implication = prop["ast"]["property"]
        self.assertEqual(implication["kind"], "SvaImplication")
        self.assertEqual(implication["antecedent"]["test"], {
            "kind": "SvaExpr",
            "expr": {"kind": "Binary", "op": "&&",
                      "left": {"kind": "Ident", "name": "a"},
                      "right": {"kind": "Ident", "name": "b"}},
        })
        self.assertEqual(implication["consequent"]["test"], {
            "kind": "SvaExpr",
            "expr": {"kind": "Binary", "op": "||",
                      "left": {"kind": "Unary", "op": "!",
                               "operand": {"kind": "Ident", "name": "c"}},
                      "right": {"kind": "Binary", "op": "===",
                                "left": {"kind": "Ident", "name": "a"},
                                "right": {"kind": "Ident", "name": "b"}}},
        })

    def test_qualified_signal_path_stays_one_observation_key(self):
        source = """module leaf(input logic a, output logic flag);
  assign flag = a;
endmodule
module top(input logic clk, a, output logic q);
  leaf u (.a(a), .flag(q));
  assert property (@(posedge clk) u.flag == a);
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "scoped.sv"
            out = Path(directory) / "scoped.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            prop = json.loads(out.read_text())["design"]["modules"][0]["properties"][0]
        test = prop["ast"]["property"]["body"]["test"]
        self.assertEqual(test["kind"], "SvaValueEq")
        self.assertEqual(test["left"]["expr"], {"kind": "Ident", "name": "u.flag"})
        self.assertEqual(test["right"]["expr"], {"kind": "Ident", "name": "a"})

    def test_reduction_expression_uses_existing_reduce_vocabulary(self):
        source = """module top(input logic clk, input logic [3:0] a, output logic q);
  assign q = |a;
  assert property (@(posedge clk) (|a) == q);
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "reduce.sv"
            out = Path(directory) / "reduce.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            prop = json.loads(out.read_text())["design"]["modules"][0]["properties"][0]
        test = prop["ast"]["property"]["body"]["test"]
        self.assertEqual(test["kind"], "SvaValueEq")
        self.assertEqual(test["left"]["expr"], {
            "kind": "Reduce", "op": "|",
            "operand": {"kind": "Ident", "name": "a"},
        })

    def test_dynamic_packed_select_is_source_shaped(self):
        source = """module top(input logic clk, input logic [3:0] a,
  input logic [1:0] i, output logic q);
  assign q = a[i];
  assert property (@(posedge clk) a[i] == q);
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "select.sv"
            out = Path(directory) / "select.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            prop = json.loads(out.read_text())["design"]["modules"][0]["properties"][0]
        test = prop["ast"]["property"]["body"]["test"]
        self.assertEqual(test["kind"], "SvaValueEq")
        self.assertEqual(test["left"]["expr"], {
            "kind": "BitSel", "value": {"kind": "Ident", "name": "a"},
            "index": {"kind": "Ident", "name": "i"},
        })

    def test_indexed_part_select_and_vector_literal_are_source_shaped(self):
        source = """module top(input logic clk, input logic [7:0] a,
  input logic [2:0] base);
  assert property (@(posedge clk) a[base +: 2] == 2'b01);
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "part.sv"
            out = Path(directory) / "part.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            prop = json.loads(out.read_text())["design"]["modules"][0]["properties"][0]
        test = prop["ast"]["property"]["body"]["test"]
        self.assertEqual(test["left"]["expr"], {
            "kind": "PartSel", "value": {"kind": "Ident", "name": "a"},
            "msb": {"kind": "Binary", "op": "+",
                    "left": {"kind": "Ident", "name": "base"},
                    "right": {"kind": "Binary", "op": "-",
                               "left": {"kind": "Int", "value": 2},
                               "right": {"kind": "Int", "value": 1}}},
            "lsb": {"kind": "Ident", "name": "base"},
        })
        self.assertEqual(test["right"]["expr"], {
            "kind": "Literal", "span": None, "width": 2, "bits": "01"})

    def test_parameter_sized_cast_stays_in_sampled_value_tree(self):
        source = """module top #(parameter int N = 8)
  (input logic clk, input logic [N-1:0] a, output logic q);
  assign q = a[0];
  assert property (@(posedge clk) a |-> a > (N'(1) << $past(a)));
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "param_cast.sv"
            out = Path(directory) / "param_cast.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            prop = json.loads(out.read_text())["design"]["modules"][0]["properties"][0]
        value = prop["ast"]["property"]["consequent"]["test"]["right"]
        self.assertEqual(value["kind"], "SvaValueBinary")
        self.assertEqual(value["left"], {
            "kind": "SvaParamCast", "parameter": "N",
            "value": {"kind": "SvaCurrent", "expr": {"kind": "Int", "value": 1}},
        })


if __name__ == "__main__":
    unittest.main()
