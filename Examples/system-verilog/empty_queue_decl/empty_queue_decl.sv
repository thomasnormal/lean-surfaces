/* An empty queue initializer has no represented time-zero state. */
module top;
  bit values[$] = {};
  int values2[$] = '{};
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
