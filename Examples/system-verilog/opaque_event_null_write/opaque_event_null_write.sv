/* Clearing an event handle has no represented self-check state. */
module top;
  event handle;
  initial begin
    handle = null;
    $display("PASS");
    $finish;
  end
endmodule
