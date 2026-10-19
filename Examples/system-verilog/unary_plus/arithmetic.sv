module unary_plus_arithmetic;
  logic [3:0] value;
  logic signed [3:0] signed_value;
  logic signed [7:0] extended;
  logic [64:0] wide;
  logic scalar;
  initial begin
    value = 4'b10xz;
    if (+value !== 4'bxxxx) $display("FAIL partial");
    value = 4'bzzzz;
    if (+value !== 4'bxxxx) $display("FAIL highz");
    value = 4'b1010;
    if (+value !== 4'b1010) $display("FAIL known");
    scalar = 1'bz;
    if (+scalar !== 1'bx) $display("FAIL scalar");
    signed_value = -4'sd3;
    extended = +signed_value;
    if (extended !== -8'sd3) $display("FAIL signed");
    signed_value = 4'b1x01;
    extended = +signed_value;
    if (extended !== 8'bxxxxxxxx) $display("FAIL extended");
    wide = 65'd17;
    if (+wide !== 65'd17) $display("FAIL wide-known");
    wide = 65'bz;
    if (+wide !== 65'bx) $display("FAIL wide-highz");
    value = 4'b0x01;
    if ({+value} !== 4'bxxxx) $display("FAIL concat");
    if ((+value & 4'b1000) !== 4'bx000) $display("FAIL nested");
    if ((+value / 4'b0010) !== 4'bxxxx) $display("FAIL division");
    $display("PASS");
    $finish;
  end
endmodule
// REFERENCE: 42035da6debc99f03cf08cc2 24.03-s004 2026-10-19T13:31:48Z | tests=unary-plus-arithmetic | source=arithmetic.sv@sha256:355d03e32ada698cd4c64d194e9dc4b77a0a6742fe8b04d51cce0d2e796bb40a | top=unary_plus_arithmetic | args=[] | map=docs/sv-unary-arithmetic.md#oracle
