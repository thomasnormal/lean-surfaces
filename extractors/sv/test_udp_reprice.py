"""Shape checks for the UDP repricing instrument."""
import unittest

from udp_reprice import udp_features


class UdpReprice(unittest.TestCase):
    def test_declaration_and_table_shapes(self):
        self.assertEqual(
            udp_features("primitive p(o,a); output o; input [1:0] a; "
                         "table 0 : 0; endtable endprimitive"),
            ("port-shape-diagnostic",))
        self.assertEqual(
            udp_features("primitive p(o,a,b); output o; input a,b; "
                         "table 0 ? : ? : 0; endtable endprimitive"),
            ("combinational-current-state-field",))
        self.assertEqual(
            udp_features("primitive p(o,a,b); output o; input a,b;\n"
                         "table\n x x : 0;\n endtable endprimitive"),
            ("all-x-input-non-x-output",))

    def test_transition_and_field_shapes(self):
        self.assertEqual(
            udp_features("primitive p(q,a,b); output q; reg q; input a,b; "
                         "table\n (01) (10) : ? : 1;\n endtable endprimitive"),
            ("multiple-transitions",))
        self.assertEqual(
            udp_features("primitive p(q,a,b); output q; reg q; input a,b; "
                         "table\n (01) : ? : 1;\n endtable endprimitive"),
            ("missing-input-field",))
        self.assertEqual(
            udp_features("primitive p(o,a); output o; input a; "
                         "table\n z : x;\n endtable endprimitive"),
            ("z-table-symbol",))

    def test_diagnostics_and_init(self):
        self.assertEqual(
            udp_features("primitive p(q,a,b); output q; reg q; input a,b; "
                         "initial q = 1'bz; table 0 0 : ? : 0; "
                         "endtable endprimitive"),
            ("invalid-init-value",))
        self.assertEqual(
            udp_features("primitive p(q,a,b); output q; reg q; input a,b; "
                         "table\n r 1 : ? : 1;\n r 1 : ? : 0;\n endtable "
                         "endprimitive"),
            ("duplicate-input-different-output",))


if __name__ == "__main__":
    unittest.main()
