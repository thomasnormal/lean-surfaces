/* Discarded zero-argument integer time queries are inert at time zero. */
module top;
  initial begin
    $time;
    $stime;
    $display("PASS");
    $finish;
  end
endmodule
