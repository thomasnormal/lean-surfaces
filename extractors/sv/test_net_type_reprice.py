"""Shape checks for NetSymbol:type repricing."""
import unittest

from net_type_reprice import net_type_features


class NetTypeReprice(unittest.TestCase):
    def test_unpacked_and_generated_net_arrays(self):
        self.assertEqual(
            net_type_features("wire logic [7:0] bus [0:3];", "bus"),
            ("multidimensional-net-array",))
        self.assertEqual(
            net_type_features("wire [2:0] t [1:3]; for (i=0; i<3; i=i+1) "
                              "assign t[1][i]=1'b1;", "t"),
            ("multidimensional-net-array", "generated-net-array"))

    def test_packed_struct_net(self):
        self.assertEqual(
            net_type_features("wire struct packed { logic [3:0] i; } sv;",
                              "sv"),
            ("packed-struct-net",))

    def test_typedef_net_shape(self):
        self.assertEqual(
            net_type_features("typedef struct packed { logic [7:0] data; } T; "
                              "wire T w;", "w"),
            ("typedef-struct-net",))


if __name__ == "__main__":
    unittest.main()
