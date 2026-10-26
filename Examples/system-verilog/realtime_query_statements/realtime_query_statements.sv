/* A discarded zero-argument realtime query is inert at time zero. */
module top;
  initial begin
    $realtime;
    $display("PASS");
    $finish;
  end
endmodule
