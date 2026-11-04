/* An empty queue literal has no represented time-zero state. */
module top;
  int q[$];
  initial begin
    q = {};
    $display("PASS");
    $finish;
  end
endmodule
