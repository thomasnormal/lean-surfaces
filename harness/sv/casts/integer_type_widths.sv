module top;
  logic signed [3:0] signed_source;
  logic [3:0] unsigned_source;
  byte byte_result;
  byte unsigned_source_result;
  shortint short_result;
  int int_result;
  longint long_result;
  integer integer_result;
  time time_result;

  initial begin
    signed_source = 4'b1001;
    unsigned_source = 4'b1001;
    byte_result = byte'(signed_source);
    unsigned_source_result = byte'(unsigned_source);
    short_result = shortint'(signed_source);
    int_result = int'(signed_source);
    long_result = longint'(signed_source);
    integer_result = integer'(signed_source);
    time_result = time'(signed_source);
    $display("integer-types=[%h][%h][%h][%h][%h][%h][%h]", byte_result,
             short_result, int_result, long_result, integer_result, time_result,
             unsigned_source_result);
    if ((byte_result === 8'hf9) && (unsigned_source_result === 8'h09) &&
        (short_result === 16'hfff9) &&
        (int_result === 32'hfffffff9) &&
        (long_result === 64'hfffffffffffffff9) &&
        (integer_result === 32'hfffffff9) &&
        (time_result === 64'hfffffffffffffff9) &&
        (byte'(signed_source) < 0) &&
        (shortint'(signed_source) < 0) &&
        (int'(signed_source) < 0) &&
        (longint'(signed_source) < 0) &&
        (integer'(signed_source) < 0) &&
        !(time'(signed_source) < 0))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 700aa6343c93bff1b9f9a3b6 TOOL:	xrun(64)	24.03-s004 2026-10-09T21:34:26Z
