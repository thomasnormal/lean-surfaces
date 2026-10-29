// INT-class targets (`integer`/`int` localparams, an `integer` parameter
// default) of a narrow unsigned operand (round 4 folds, verifier repros
// rf_int/rf_ipar): the initializer is an assignment to a 32-bit target, so
// it is evaluated at max(32, its own width) at every point (IEEE 1800-2023
// 10.8, 11.8.1): `U + 1'b1` with U = -1 is 16 at N = 4 and 256 at N = 8 in
// Icarus 12.0 and the Yosys 0.53 netlist (the model read 0 at both).
module fold_rint #(parameter int N = 32, parameter logic [N-1:0] U = -1,
                   parameter integer P = U + 1'b1) (
  input  logic [31:0] v,
  output logic [31:0] o1,
  output logic o2,
  output logic [31:0] o3,
  output logic [31:0] o4);
  localparam integer L = U + 1'b1;
  localparam int K = U + 1'b1;
  assign o1 = L;
  assign o2 = v[L[4:0]];
  assign o3 = P;
  assign o4 = K;
endmodule
