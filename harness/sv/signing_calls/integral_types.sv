module top;
  typedef logic signed [3:0] small_t;
  typedef enum logic [3:0] {NEGATIVE = 4'b1110} code_t;
  small_t small_value;
  code_t code;
  byte signed_byte;
  shortint signed_short;
  int signed_int;
  longint signed_long;
  logic [31:0] unsigned_int;
  logic [63:0] unsigned_long;

  initial begin
    small_value = 4'b1100;
    code = NEGATIVE;
    signed_byte = -8'sd2;
    signed_short = $signed(signed_byte);
    signed_int = $signed(small_value);
    signed_long = $signed(code);
    unsigned_int = $unsigned(signed_byte);
    unsigned_long = $unsigned(signed_int);
    $display("signed=%0d unsigned=%0d", $signed(small_value), $unsigned(small_value));
    if ((signed_short === -16'sd2) && (signed_int === -32'sd4) &&
        (signed_long === -64'sd2) && (unsigned_int === 32'h000000fe) &&
        (unsigned_long === 64'h00000000fffffffc) &&
        ($bits($signed(signed_byte)) === 32'd8) &&
        ($bits($unsigned(signed_long)) === 32'd64))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 8d03a6b96b4f457c13814ed5 independent-simulator 2026-10-11T16:23:48Z
