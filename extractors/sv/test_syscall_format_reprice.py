import unittest
from syscall_format_reprice import format_features
class SyscallFormatReprice(unittest.TestCase):
    def test_macro_defaults(self): self.assertIn('macro-default-arguments',format_features('`define M(a=1,b) $display(a,b)'))
    def test_macro_expansion(self): self.assertIn('macro-expansion',format_features('`define M(a) $display(a)'))
    def test_runtime_display(self): self.assertEqual(format_features('$display(p);'),('runtime-display-format',))
if __name__=='__main__': unittest.main()
