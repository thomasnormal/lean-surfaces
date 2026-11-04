// An out-of-range INNER index of a packed array: per IEEE 1800-2023 7.4.6
// and 11.5.1 each index is checked against its own dimension, so m[0][4]
// reads x and w[0][5] writes nothing (slang's constant evaluator agrees).
// Icarus 12.0 and Yosys 0.53 linearize instead (m[1][0], w[1][1]).
module array_oob_inner (
  input  logic [3:0] a,
  output logic [7:0] w_flat,
  output logic       z
);
  logic [1:0][3:0] m;
  logic [1:0][3:0] w;
  assign m[0] = a;
  assign m[1] = ~a;
  assign z = m[0][4];
  always_comb begin
    w = 8'h00;
    w[0][5] = 1'b1;
  end
  assign w_flat = w;
endmodule
