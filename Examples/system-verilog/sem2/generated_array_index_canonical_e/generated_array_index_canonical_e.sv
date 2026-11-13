module generated_array_index_canonical_e
  (input logic [7:0] x, output logic [7:0] y);
  logic [7:0] slot [0:3];
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : g
      assign slot[i] = x;
    end
  endgenerate
  assign y = slot[0];
endmodule
