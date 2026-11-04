import unittest
from namedvalue_2state_reprice import namedvalue_features
class NamedValueReprice(unittest.TestCase):
    def test_foreach(self): self.assertIn('fixed-array-foreach',namedvalue_features('foreach (arr[i]) begin end'))
    def test_literal(self): self.assertIn('array-literal-context',namedvalue_features("triple t; t = '{1,2,3};"))
    def test_indexed(self): self.assertIn('indexed-array-pattern',namedvalue_features("arr = '{0:1, 1:2};"))
if __name__=='__main__':unittest.main()
