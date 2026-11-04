/* A pure real literal write updates opaque storage with no self-check state. */
module top;
  real value;
  initial begin
    value = -3.5;
    $display("PASS");
    $finish;
  end
endmodule
