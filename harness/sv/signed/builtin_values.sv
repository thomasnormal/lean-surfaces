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

  initial begin
    byte_signed = -1;
    byte_unsigned = byte_signed;
    short_signed = byte_signed;
    short_unsigned = byte_unsigned;
    int_signed = short_signed;
    int_unsigned = short_unsigned;
    long_signed = int_signed;
    long_unsigned = int_unsigned;
    integer_signed = long_signed;
    integer_unsigned = long_unsigned;
    time_unsigned = integer_signed;
    time_signed = integer_unsigned;
    $display("byte=[%0d][%0d]", byte_signed, byte_unsigned);
    $display("shortint=[%0d][%0d]", short_signed, short_unsigned);
    $display("int=[%0d][%0d]", int_signed, int_unsigned);
    $display("longint=[%0d][%0d]", long_signed, long_unsigned);
    $display("integer=[%0d][%0d]", integer_signed, integer_unsigned);
    $display("time=[%0d][%0d]", time_unsigned, time_signed);
    $finish;
  end
endmodule
