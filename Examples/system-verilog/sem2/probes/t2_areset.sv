// Phase-2 probe: async active-low reset (two-edge sensitivity) with a
// downstream FF — the pre-edge visibility rows (pin3) as a harness case.
module t2_areset (
    input  logic clk, rst_n,
    input  logic [3:0] d,
    output logic [3:0] q,
    output logic [3:0] q2
);
  always_ff @(posedge clk or negedge rst_n) begin
    if (~rst_n) q <= '0;
    else q <= d;
  end
  always_ff @(posedge clk) q2 <= q;
endmodule
