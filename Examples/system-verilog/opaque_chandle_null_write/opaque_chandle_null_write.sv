/* Clearing a chandle has no represented self-check state. */
module top;
  chandle handle;
  initial begin
    handle = null;
    $display("PASS");
    $finish;
  end
endmodule
