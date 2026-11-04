// WP-B2 gate 2b pin P10: the six comparisons of two 4-bit operands: a known mismatch decides `==`/`!=` even with an x elsewhere; every ordering comparison with an x/z bit in either operand is x.
module wl_cmp_same (
  input  logic [3:0] a,
  input  logic [3:0] b,
  output logic eq,
  output logic ne,
  output logic lt,
  output logic le,
  output logic gt,
  output logic ge
);
  assign eq = a == b;
  assign ne = a != b;
  assign lt = a < b;
  assign le = a <= b;
  assign gt = a > b;
  assign ge = a >= b;
endmodule
