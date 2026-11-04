/* A single literal continuous driver may target one constant packed bit. */
module top;
  wire [3:0] bus;
  assign bus[2] = 1'b1;
  initial begin
    if (bus[2] === 1'b1 && bus[1] === 1'bz)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
