/* A module-scope real declaration is inert on the time-zero self-check path. */
module top;
  real rr;
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
