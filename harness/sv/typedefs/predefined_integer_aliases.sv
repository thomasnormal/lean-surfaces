module top;
  typedef byte byte_alias_t;
  typedef shortint short_alias_t;
  typedef int int_alias_t;
  typedef longint long_alias_t;
  typedef integer integer_alias_t;
  typedef time time_alias_t;
  logic signed [3:0] source_value;
  byte_alias_t byte_value;
  short_alias_t short_value;
  int_alias_t int_value;
  long_alias_t long_value;
  integer_alias_t integer_value;
  time_alias_t time_value;

  initial begin
    source_value = 4'h9;
    byte_value = byte_alias_t'(source_value);
    short_value = short_alias_t'(source_value);
    int_value = int_alias_t'(source_value);
    long_value = long_alias_t'(source_value);
    integer_value = integer_alias_t'(source_value);
    time_value = time_alias_t'(source_value);
    $display("predefined-alias=[%h][%h][%h][%h][%h][%h]", byte_value,
             short_value, int_value, long_value, integer_value, time_value);
    if ((byte_value === 8'hf9) && (short_value === 16'hfff9) &&
        (int_value === 32'hfffffff9) &&
        (long_value === 64'hfffffffffffffff9) &&
        (integer_value === 32'hfffffff9) &&
        (time_value === 64'hfffffffffffffff9) &&
        (byte_value < 0) && (short_value < 0) &&
        (int_value < 0) && (long_value < 0) &&
        (integer_value < 0) && !(time_value < 0))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
