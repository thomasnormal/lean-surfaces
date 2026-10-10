"""IEEE 1800-2023 section 20.9 admission; licensed fixtures pin runtime values."""

import unittest

from test_bit_queries import REPO, lower, nodes, query_source


CALLS = ("$countbits", "$countones", "$onehot", "$onehot0", "$isunknown")


def queries(design):
    return [node for node in nodes(design) if node.get("kind") == "BitQuery"]


class BitVectorQueries(unittest.TestCase):
    def test_all_query_signatures(self):
        for name in CALLS:
            with self.subTest(name=name):
                arguments = "value, 1'b1" if name == "$countbits" else "value"
                design = lower(query_source(name + "(" + arguments + ")",
                                            "logic [7:0] value; "))
                query = queries(design)[0]
                count_query = name in ("$countbits", "$countones")
                self.assertEqual(query["op"], name)
                self.assertEqual(query["width"], 32 if count_query else 1)
                self.assertEqual(query.get("signed", False), count_query)
                self.assertEqual(len(query["controls"]), 1 if name == "$countbits" else 0)
                self.assertEqual(query["operand"]["width"], 8)

    def test_controls_stay_runtime_expressions_at_original_width(self):
        design = lower(query_source("$countbits(value, control, control)",
                                    "logic [5:0] value; logic [2:0] control; "))
        query = queries(design)[0]
        self.assertEqual([control["width"] for control in query["controls"]], [3, 3])
        self.assertEqual([control["name"] for control in query["controls"]],
                         ["control", "control"])

    def test_original_licensed_fixtures_are_fully_admitted(self):
        for path in sorted((REPO / "harness/sv/bit_vector_queries").glob("*.sv")):
            with self.subTest(path=path.name):
                design = lower(path.read_text())
                self.assertTrue(queries(design))
                self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_queries_survive_conversions_in_invalid_compilations(self):
        source = ("module top; logic [63:0] value; initial value = $countones(8'hff); "
                  "endmodule module bad; initial undeclared = 1; endmodule")
        design = lower(source, require_valid=False)
        self.assertTrue(queries(design))
        self.assertIn("BitQuery:invalid-compilation",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_invalid_query_forms_stay_loud(self):
        for expression in ("$countbits()", "$countbits(8'hff)", "$countones()",
                           "$onehot(1, 2)", "$isunknown(undeclared)"):
            with self.subTest(expression=expression):
                design = lower(query_source(expression), require_valid=False)
                self.assertTrue(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_nonintegral_and_effectful_arguments_stay_loud(self):
        for declaration, expression in (
            ("real value; ", "$countones(value)"),
            ("logic [7:0] value [2]; ", "$countones(value)"),
            ("logic [7:0] value; ", "$countones(value++)"),
            ("logic [7:0] value; ", "$countbits(value, value++)"),
        ):
            with self.subTest(expression=expression):
                design = lower(query_source(expression, declaration), require_valid=False)
                self.assertTrue(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_escaped_user_function_is_not_a_system_query(self):
        source = ("module top; function automatic int \\$countones (int value); "
                  "return value; endfunction initial $display(\"%0d\", \\$countones (7)); endmodule")
        self.assertFalse(queries(lower(source)))

    def test_symbolic_path_is_unchanged(self):
        import extract
        from pyslang.ast import Compilation
        from pyslang.syntax import SyntaxTree

        source = "module top; logic [7:0] value; initial value = $countones(value); endmodule"
        tree = SyntaxTree.fromText(source)
        compilation = Compilation()
        compilation.addSyntaxTree(tree)
        compilation.getAllDiagnostics()
        extract._SOURCE_BYTES = source.encode()
        extract._SYM = extract.SymCtx(compilation, tree.sourceManager, {})
        try:
            design = extract.convert_design(tree.sourceManager, compilation)
        finally:
            extract._SYM = None
        self.assertFalse(queries(design))


if __name__ == "__main__":
    unittest.main()
