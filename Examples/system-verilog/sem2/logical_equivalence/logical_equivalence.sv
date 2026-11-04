// Scalar logical equivalence lowers to existing four-state logical nodes.
module logical_equivalence (
  input  logic a,
  input  logic b,
  output logic y
);
  always_comb y = a <-> b;
endmodule
