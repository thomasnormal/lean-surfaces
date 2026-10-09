module top;
  byte byte_signed;
  byte unsigned byte_unsigned;
  shortint short_signed;
  shortint unsigned short_unsigned;
  int int_signed;
  int unsigned int_unsigned;
  longint long_signed;
  longint unsigned long_unsigned;
  integer integer_signed;
  integer unsigned integer_unsigned;
  time time_unsigned;
  time signed time_signed;
  logic signed logic_scalar;
  bit signed bit_scalar;
  reg signed [3:0] reg_packed;
  bit signed [3:0] bit_packed;

  initial begin
    $display("byte=[%b][%b]", byte_signed, byte_unsigned);
    $display("shortint=[%b][%b]", short_signed, short_unsigned);
    $display("int=[%b][%b]", int_signed, int_unsigned);
    $display("longint=[%b][%b]", long_signed, long_unsigned);
    $display("integer=[%b][%b]", integer_signed, integer_unsigned);
    $display("time=[%b][%b]", time_unsigned, time_signed);
    $display("scalar=[%b][%b] packed=[%b][%b]", logic_scalar, bit_scalar,
             reg_packed, bit_packed);
    $finish;
  end
endmodule
