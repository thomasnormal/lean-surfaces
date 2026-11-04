module top;
  byte byte_value;
  shortint short_value;
  int int_value;
  longint long_value;
  integer integer_value;
  time signed time_value;
  logic signed [3:0] packed_value;
  logic signed scalar_value;

  initial begin
    byte_value = -1;
    short_value = -1;
    int_value = -1;
    long_value = -1;
    integer_value = -1;
    time_value = -1;
    packed_value = -1;
    scalar_value = 1'b1;
    $display("byte=[%d][%0d] short=[%d][%0d]", byte_value, byte_value,
             short_value, short_value);
    $display("int=[%d][%0d] integer=[%d][%0d]", int_value, int_value,
             integer_value, integer_value);
    $display("long=[%d][%0d] time=[%d][%0d]", long_value, long_value,
             time_value, time_value);
    $display("packed=[%d][%0d] scalar=[%d][%0d]", packed_value, packed_value,
             scalar_value, scalar_value);
    byte_value = 8'sb10000000;
    short_value = 16'sb1000000000000000;
    int_value = 32'sb10000000000000000000000000000000;
    long_value = 64'sb1000000000000000000000000000000000000000000000000000000000000000;
    $write("min-byte=[%d][%0d] ", byte_value, byte_value);
    $display("min-short=[%d][%0d]", short_value, short_value);
    $display("min-int=[%d][%0d] min-long=[%d][%0d]", int_value, int_value,
             long_value, long_value);
    $finish;
  end
endmodule
