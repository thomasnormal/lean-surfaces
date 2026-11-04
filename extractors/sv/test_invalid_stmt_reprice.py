"""Shape checks for the InvalidStatement repricing instrument."""
import unittest

from invalid_stmt_reprice import invalid_shape


class InvalidStatementReprice(unittest.TestCase):
    def test_recovery_shapes(self):
        self.assertEqual(invalid_shape("begin\n  $finish;\nend"),
                         "bad begin/block recovery")
        self.assertEqual(invalid_shape("$my_vpi_task;"),
                         "VPI system-task token")

    def test_empty_and_other_stay_loud(self):
        self.assertEqual(invalid_shape(""), "empty frontend span")
        self.assertEqual(invalid_shape("not a known statement"),
                         "other bad statement")


if __name__ == "__main__":
    unittest.main()
