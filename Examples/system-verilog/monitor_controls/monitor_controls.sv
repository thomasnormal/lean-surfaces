/* Monitor toggles without a registration have no self-check observable state. */
module top;
  initial begin
    $monitoroff;
    $monitoron();
    $display("PASS");
    $finish;
  end
endmodule
