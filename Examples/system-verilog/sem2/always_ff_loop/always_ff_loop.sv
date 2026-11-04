// A literal procedural loop inside always_ff updates each vector bit at the edge.
module always_ff_loop (
  input logic clk,
  input logic [1:0] d,
  output logic [1:0] q
);
  always_ff @(posedge clk) begin
    for (int i = 0; i < 2; i++)
      q[i] <= d[i];
  end
endmodule
