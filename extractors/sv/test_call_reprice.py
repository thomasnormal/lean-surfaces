"""Shape classifier checks for the call-statement repricing instrument."""
import unittest

from call_reprice import call_shape


class CallReprice(unittest.TestCase):
    def test_system_task_heads(self):
        self.assertEqual(call_shape('$fatal(1, "bad");'), "$fatal")
        self.assertEqual(call_shape('$dumpvars(0, top);'), "$dumpvars")

    def test_void_cast_and_member_calls(self):
        self.assertEqual(call_shape("void'(std::randomize(a));"),
                         "void-cast callable")
        self.assertEqual(call_shape("payload.reverse();"),
                         "member method call")

    def test_unclassified_text_stays_loud(self):
        self.assertEqual(call_shape("?"), "unclassified call")


if __name__ == "__main__":
    unittest.main()
