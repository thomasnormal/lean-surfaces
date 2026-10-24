/* A zero-key semaphore construction is opaque in the self-check tier. */
module top;
  semaphore sem;
  initial begin
    sem = new(0);
    $display("PASS");
    $finish;
  end
endmodule
