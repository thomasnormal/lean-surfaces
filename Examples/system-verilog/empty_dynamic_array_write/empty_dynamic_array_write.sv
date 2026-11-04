/* A zero-item dynamic-array literal has no represented time-zero state. */
module top;
  int values[];
  initial begin
    values = {};
    $display("PASS");
    $finish;
  end
endmodule
