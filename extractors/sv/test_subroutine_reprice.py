"""Shape checks for the subroutine repricing instrument."""
import unittest

from subroutine_reprice import subroutine_shape


class SubroutineReprice(unittest.TestCase):
    def test_function_and_task_declarations(self):
        self.assertEqual(
            subroutine_shape("function automatic int f(input int x); return x; endfunction"),
            "function declaration")
        self.assertEqual(
            subroutine_shape("task automatic t(); #1; endtask"),
            "task declaration")

    def test_dpi_import_is_external(self):
        self.assertEqual(
            subroutine_shape('import "DPI-C" function int f(input int x);'),
            "DPI import")

    def test_unknown_text_stays_loud(self):
        self.assertEqual(subroutine_shape("subroutine ???"), "other subroutine")


if __name__ == "__main__":
    unittest.main()
