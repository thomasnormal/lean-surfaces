/* A pure integral-to-real write updates only opaque floating storage. */
module top;
  int source;
  real real_value;
  shortreal short_value;
  initial begin
    source = 42;
    real_value = source;
    real_value = real'(source);
    short_value = source;
    short_value = shortreal'(source);
    $display("PASS");
    $finish;
  end
endmodule
