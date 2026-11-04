import unittest
from parameter_scope_reprice import parameter_features
class ParameterScopeReprice(unittest.TestCase):
    def test_unit(self): self.assertIn('compilation-unit-parameter',parameter_features('parameter int U=1; module top; endmodule'))
    def test_explicit_unit(self): self.assertIn('explicit-unit-reference',parameter_features('parameter int U=1; module m #(parameter W=$unit::U); endmodule'))
    def test_declaration(self): self.assertIn('unit-declaration',parameter_features('localparam int U=1;'))
if __name__=='__main__':unittest.main()
