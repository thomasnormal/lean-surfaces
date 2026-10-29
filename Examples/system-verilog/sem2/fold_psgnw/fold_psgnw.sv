// Round 5 folds (verifier repro vq_sgn2, wide points): a signed parameter
// whose default width is 32 (where the envelope used to omit its `signed`
// field), read at widths above 32 in value positions — sign-extended in
// Icarus 12.0 and the Yosys 0.53 netlist. (`fold_psgn` covers the narrow
// points; its `integer` localparam narrows S here, which the cross-check's
// point extraction does not admit.)
module fold_psgnw #(parameter int M = 32, parameter logic signed [M-1:0] S = -1) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2, o3,
  output logic o4);
  assign o1 = S;
  assign o2 = S + a;
  assign o3 = S >>> 1;
  assign o4 = S < 0;
endmodule
