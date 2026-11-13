// Clean-room canonical-E fixture for packed bit-select bases.
module bit_select_canonical_e #(parameter int W = 8) (
  input logic [W-1:0] d,
  input logic [2:0] idx,
  output logic q0,
  output logic qidx
);
  assign q0 = d[0];
  assign qidx = d[idx];
endmodule
