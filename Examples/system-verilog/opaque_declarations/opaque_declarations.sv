/* Declaration-only opaque IEEE types are inert in the legacy self-check tier. */
// PASS
module top;
  real r = 0.5;
  realtime rt = 0.5;
  shortreal sr = 0.5;
  chandle h;
  event ev;

  initial begin
    $display("PASS");
    $finish;
  end
endmodule
