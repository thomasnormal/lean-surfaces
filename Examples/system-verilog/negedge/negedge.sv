module negedge_wait(input logic clk);
  logic [3:0] value;
  initial begin
    value = 4'd1;
    @(negedge clk);
    value = 4'd2;
    $display("PASS");
    $finish;
  end
endmodule
