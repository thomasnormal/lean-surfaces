/* Capturing the current process is opaque in the self-check tier. */
module top;
  process handle;
  initial begin
    handle = process::self();
    $display("PASS");
    $finish;
  end
endmodule
