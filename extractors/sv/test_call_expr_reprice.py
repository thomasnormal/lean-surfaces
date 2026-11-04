"""Shape classifier checks for the expression-call repricing instrument."""
import unittest

from call_expr_reprice import call_shape


class CallExpressionReprice(unittest.TestCase):
    def test_system_and_sampled_heads(self):
        self.assertEqual(call_shape("$random(seed)"), "$random")
        self.assertEqual(call_shape("$stable(sig)"), "$stable")

    def test_scope_and_member_calls(self):
        self.assertEqual(call_shape("std::randomize(a) with { a < 3; }"),
                         "scope method call")
        self.assertEqual(call_shape("color.name()"), "member method call")

    def test_void_cast_and_unclassified(self):
        self.assertEqual(call_shape("void'(std::randomize(a));"),
                         "void-cast callable")
        self.assertEqual(call_shape("?"), "unclassified call")


if __name__ == "__main__":
    unittest.main()
