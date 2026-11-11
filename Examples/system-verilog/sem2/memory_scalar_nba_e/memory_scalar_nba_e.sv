// Clean-room E memory fixture: one edge body updates a scalar and an
// unpacked-memory cell with nonblocking assignments, then continuous drivers
// expose both post-commit values.
module memory_scalar_nba_e #(parameter integer W = 8, N = 4) (
    input wire clk, rstn, input wire [W-1:0] d,
    output wire [W-1:0] q, scalar_q
);
  logic [W-1:0] mem [N];
  logic [W-1:0] scalar;
  always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) begin
      scalar <= '0;
      mem[0] <= '0;
    end else begin
      scalar <= d;
      mem[0] <= d;
    end
  end
  assign q = mem[0];
  assign scalar_q = scalar;
endmodule
