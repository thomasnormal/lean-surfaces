/* A pure all-literal integral net expression is fixed at time zero. */
module top;
  wire [3:0] driven;
  assign driven = 4'd3 * 4'd2;
  initial begin
    if (driven === 4'd6)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
