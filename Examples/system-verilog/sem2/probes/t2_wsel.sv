// Phase-2 probe: dynamic element write into a 2D packed array (NBA),
// dynamic element read; x/OOB index semantics on both sides.
module t2_wsel (
    input  logic clk,
    input  logic [1:0] wi,
    input  logic [7:0] wd,
    input  logic we,
    output logic [3:0][7:0] mem_o,
    output logic [7:0] slice_o
);
  logic [3:0][7:0] m;
  always_ff @(posedge clk) begin
    if (we) m[wi] <= wd;
  end
  assign mem_o   = m;
  assign slice_o = m[wi];
endmodule
