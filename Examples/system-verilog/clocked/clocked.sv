module clocked(input logic clk);
  logic [3:0] value;
  always @(posedge clk) begin
    value = 4'd1;
  end
endmodule
