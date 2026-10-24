/* A pure literal real initializer has no representation in self-check state. */
module top;
  initial begin
    real unused = -3.5;
    shortreal also_unused = 2.0;
    $display("PASS");
    $finish;
  end
endmodule
