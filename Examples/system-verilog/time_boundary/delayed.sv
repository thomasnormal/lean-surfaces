// A time-zero-only query must not become a constant in a timed executor.
module top;
  initial begin
    #2;
    $display("time %0d", $time);
    $finish;
  end
endmodule
