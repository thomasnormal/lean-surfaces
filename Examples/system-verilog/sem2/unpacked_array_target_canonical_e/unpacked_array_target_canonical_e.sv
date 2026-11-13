// Minimal generic witness for the current front-end boundary.
module unpacked_array_target_canonical_e(input logic [7:0] x,
  input logic idx, output logic [7:0] y);
  logic [7:0] slot [0:1];
  always_comb begin
    slot[idx] = x;
    y = slot[idx];
  end
endmodule
// End of witness.
