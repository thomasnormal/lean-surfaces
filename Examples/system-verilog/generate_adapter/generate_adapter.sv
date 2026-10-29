/* A clean elaborated generate scope is ordinary self-check state. */
// PASS
module top;
  logic value;
  if (1) begin : live
    initial value = 1'b1;
  end
  initial begin
    if (value)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
