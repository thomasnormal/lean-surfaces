/* An uninitialized procedural real has no self-check state to allocate. */
module top;
  initial begin
    real unused;
    $display("PASS");
    $finish;
  end
endmodule
