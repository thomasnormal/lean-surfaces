import unittest
from enum_invalid_reprice import enum_features
class EnumInvalidReprice(unittest.TestCase):
    def test_xz(self): self.assertIn('xz-in-two-state-base',enum_features("enum bit [1:0] {XX='x};"))
    def test_base(self): self.assertIn('two-state-enum-base',enum_features('enum bit [1:0] {A,B};'))
    def test_duplicate(self): self.assertIn('duplicate-enumeration-value',enum_features('enum {a=0,b=7,c=8,d=8};'))
if __name__=='__main__':unittest.main()
