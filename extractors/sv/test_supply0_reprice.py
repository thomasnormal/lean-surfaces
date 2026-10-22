import unittest
from supply0_reprice import supply0_features
class Supply0Reprice(unittest.TestCase):
    def test_driver(self): self.assertIn('supply-strength-driver',supply0_features('supply0 n;','supply0 n'))
    def test_zero_source(self): self.assertIn('logic-zero-source',supply0_features('supply0 gnd;','supply0 gnd'))
    def test_context(self): self.assertIn('continuous-strength-context',supply0_features('assign (supply0) n = gnd;','n'))
if __name__=='__main__': unittest.main()
