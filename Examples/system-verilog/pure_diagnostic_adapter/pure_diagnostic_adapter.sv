/* Inert pure diagnostics do not allocate legacy self-check state. */
// PASS
`timescale 1ns/1ps
module top;
  initial begin
    $printtimescale;
    $printtimescale($unit);
    $exit;
    $display("PASS");
  end
endmodule
