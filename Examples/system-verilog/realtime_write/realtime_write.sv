/* A time-zero realtime write into opaque floating storage is inert. */
module top;
  real value;
  initial begin
    value = $realtime;
    $display("PASS");
    $finish;
  end
endmodule
