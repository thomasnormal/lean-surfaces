/* Bare mailbox construction is opaque in the self-check tier. */
module top;
  mailbox box;
  initial begin
    box = new();
    $display("PASS");
    $finish;
  end
endmodule
