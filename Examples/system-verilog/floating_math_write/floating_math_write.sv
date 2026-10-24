/* Pure real math writes have no represented self-check storage. */
module top;
  real value;
  initial begin
    value = $sqrt(16.0);
    $display("PASS");
    $finish;
  end
endmodule
