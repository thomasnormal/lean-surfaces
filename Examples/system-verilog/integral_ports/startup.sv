module startup(
  input bit unsigned_bit,
  input bit signed [3:0] signed_bits,
  input int signed_integer,
  input integer four_state_integer,
  output bit [3:0] value
);
  initial begin
    if (unsigned_bit == 0 && signed_bits == 0 && signed_integer == 0)
      $display("PASS");
    else
      $display("FAIL");
    if (four_state_integer === 32'bzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz)
      $display("PASS");
    else
      $display("FAIL");
    value = 4'b1xz1;
    if (value == 4'b1001)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
