/* Clearing a named opaque handle to null has no modeled state effect. */
module top;
  mailbox box;
  initial begin
    box = null;
    $display("PASS");
    $finish;
  end
endmodule
