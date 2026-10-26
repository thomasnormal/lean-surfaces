/* A continuous driver fed by a single time-zero blocking literal write. */
module top;
  logic source;
  wire driven;
  assign driven = source;
  initial begin
    source = 1'b1;
    if (driven === 1'b1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
