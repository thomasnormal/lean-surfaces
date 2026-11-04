// Round 5 folds (round 3 verifier minor 4): an UNTYPED constant whose
// self-determined value wraps. Its type is its expression's (IEEE 1800-2023
// 6.20.2), so `SB + 1'b1` with an 8-bit SB = 255 is 0 in slang, the Yosys
// 0.53 netlist and the LRM, and 256 in Icarus 12.0 (which evaluates an
// untyped parameter value losslessly). Refused where it wraps (SB = 255;
// `SB * 2'd2` from SB = 128), run where it does not (the default SB = 5).
module fold_uovf #(parameter int N = 8, parameter logic [N-1:0] SB = 8'd5) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2);
  localparam Y = SB + 1'b1;
  localparam Z = SB * 2'd2;
  assign o1 = Y;
  assign o2 = Z + a;
endmodule
