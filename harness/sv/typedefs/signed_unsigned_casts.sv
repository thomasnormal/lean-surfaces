module top;
  typedef logic signed [3:0] signed_nibble_t;
  typedef logic [3:0] unsigned_nibble_t;
  typedef logic signed [7:0] signed_byte_t;
  typedef logic [15:0] unsigned_word_t;
  signed_nibble_t signed_source;
  unsigned_nibble_t unsigned_source;
  unsigned_word_t signed_cast_value;
  signed_byte_t unsigned_cast_value;
  unsigned_word_t mixed_sum_value;

  initial begin
    signed_source = 4'h9;
    unsigned_source = 4'h9;
    signed_cast_value = unsigned_word_t'(signed_source);
    unsigned_cast_value = signed_byte_t'(unsigned_source);
    mixed_sum_value = signed_source + unsigned_source;
    $display("alias-signs=[%h][%h][%h]", signed_cast_value,
             unsigned_cast_value, mixed_sum_value);
    if ((signed_cast_value === 16'hfff9) &&
        (unsigned_cast_value === 8'h09) &&
        (mixed_sum_value === 16'h0012) &&
        (signed_source < 0) && !(unsigned_source < 0) &&
        !(signed_cast_value < 0) && !(unsigned_cast_value < 0))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: ef390c71d6da2c597eea35a6 TOOL:	xrun(64)	24.03-s004 2026-10-09T21:34:54Z
