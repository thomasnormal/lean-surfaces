/* Output and termination calls use the existing self-check state. */
// PASS
module top;
  initial begin
    $write("PASS");
    $display("");
    $stop;
  end
endmodule
