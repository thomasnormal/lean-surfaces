"""Local fixed-unpacked arrays retain static lifetime and reset automatic cells."""
import unittest
from test_packed_assignment_targets import extract_source, nodes

class LocalArrayLifetime(unittest.TestCase):
    def test_static_and_automatic_cells_are_named_by_declaration(self):
        design = extract_source("""module top; initial begin repeat(2) begin
          static int saved [0:1] = '{4, 8};
          automatic int fresh [0:1] = '{4, 8};
          saved[0] = saved[0] + 1; fresh[0] = fresh[0] + 1;
        end end endmodule""")
        decls = [n for n in nodes(design) if n.get("kind") in ("Var", "LocalDecl")]
        self.assertEqual([d["name"].split(":")[-1] for d in decls],
                         ["saved[0]", "saved[1]", "fresh[0]", "fresh[1]"])
        self.assertEqual(len({d["name"].rsplit(":", 1)[0] for d in decls}), 2)
        self.assertTrue(all(d.get("kind") == "Var" for d in decls[:2]))
        self.assertTrue(all(d.get("automatic_array") for d in decls[2:]))
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_static_initializer_reads_are_loud(self):
        design = extract_source("""module top; int source; initial begin source=9;
          static int saved [0:0] = '{source}; end endmodule""")
        self.assertTrue(any(n.get("sv_kind") == "StaticLocal:initializer"
                            for n in nodes(design)))

    def test_noncanonical_bounds_and_bit_conversion_are_cells(self):
        design = extract_source("""module top; initial begin
          bit [3:0] value [-1:1] = '{4'b1xz0, 4'h5, 4'ha};
          if (value[-1] == 0 && value[0] == 5 && value[1] == 10) $display(\"PASS\");
        end endmodule""")
        decls = [n for n in nodes(design) if n.get("kind") == "Var"]
        self.assertEqual([d["name"].split(":")[-1] for d in decls],
                         ["value[-1]", "value[0]", "value[1]"])
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_scope_declarations_do_not_alias(self):
        design = extract_source("""module top; initial begin
          begin static int x [0:0] = '{2}; end
          begin static int x [0:0] = '{7}; end
        end endmodule""")
        names = [n["name"] for n in nodes(design) if n.get("kind") == "Var"]
        self.assertEqual(len(names), 2)
        self.assertNotEqual(names[0], names[1])

    def test_automatic_initializer_retains_entry_time_read(self):
        design = extract_source("""module top; int source; initial begin
          repeat(2) begin automatic int fresh [0:0] = '{source}; end
        end endmodule""")
        cells = [n for n in nodes(design) if n.get("kind") == "LocalDecl"]
        self.assertEqual(len(cells), 1)
        self.assertTrue(any(n.get("kind") == "Ident" and n.get("name") == "source"
                            for n in nodes(cells[0]["init"])))
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_generated_storage_collision_stays_loud(self):
        prefix = "module top; initial begin static int x [0:0] = '{2}; end "
        original = extract_source(prefix + "endmodule")
        name, = [n["name"] for n in nodes(original) if n.get("kind") == "Var"]
        design = extract_source(prefix + "int \\" + name + " ; endmodule")
        self.assertTrue(any(n.get("sv_kind") == "VariableDeclStatement:array-storage-collision"
                            for n in nodes(design)))

    def test_repeated_extraction_is_identical(self):
        source = """module top; initial begin
          static int saved [0:0] = '{2};
          automatic int fresh [0:0] = '{4};
        end endmodule"""
        self.assertEqual(extract_source(source), extract_source(source))

if __name__ == "__main__": unittest.main()
