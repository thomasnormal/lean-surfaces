/* A continuous driver fed by an immutable literal variable is time-zero fixed. */
module top;
  logic source = 1'b1;
  wire driven;
  assign driven = source;
  initial begin
    if (driven === 1'b1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
