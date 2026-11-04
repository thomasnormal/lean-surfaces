// Concurrent assertions are retained as property metadata while the
// sequential body remains an ordinary E-process.
module sva_property_retained (
    input logic clk,
    input logic rst_n,
    input logic a,
    input logic b,
    output logic q
);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) q <= 1'b0;
    else q <= a;
  end

  assert property (@(posedge clk) disable iff (!rst_n) a |-> b);
  assume property (@(posedge clk) a |=> b);
  cover property (@(posedge clk) a ##1 b);
endmodule
