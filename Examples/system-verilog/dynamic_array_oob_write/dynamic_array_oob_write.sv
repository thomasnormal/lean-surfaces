/* A constant out-of-range dynamic-array write is a no-op. */
module top;
  bit values[];
  initial begin
    values = new[2];
    values[4] = 1'b1;
    if (values[0] === 1'b0 && values[1] === 1'b0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
