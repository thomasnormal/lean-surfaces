// Minimal generic witness for the current front-end boundary.
module generate_if_unpacked_array_canonical_e #(parameter integer N = 2)
  (input logic [7:0] x, output logic [7:0] y);
  if (N > 0) begin : g
    logic [7:0] stage [0:N-1];
    assign stage[0] = x;
    assign y = stage[0];
  end
endmodule
// End of witness.
