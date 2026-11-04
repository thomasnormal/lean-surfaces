/* An uninitialized class handle is null metadata until a modeled use occurs. */
module top;
  mailbox module_box;
  initial begin
    mailbox local_box;
    $display("PASS");
    $finish;
  end
endmodule
