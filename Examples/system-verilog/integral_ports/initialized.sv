module initialized(
  input bit defaulted_bit = 1'b1,
  input int defaulted_integer = 7,
  output bit [3:0] initialized_value = 4'b1xz1
);
  initial begin
    if (defaulted_bit == 1'b1 && defaulted_integer == 7 && initialized_value == 4'b1001)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
