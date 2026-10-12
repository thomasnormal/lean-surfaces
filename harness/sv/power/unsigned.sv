module top;
  logic [7:0] base;
  logic [3:0] exponent;
  logic [31:0] large_exponent;
  logic [15:0] wide_result;
  logic [3:0] narrow_result;
  initial begin
    base = 3;
    exponent = 5;
    if ((base ** exponent) !== 8'd243) $display("FAIL positive");
    exponent = 0;
    if ((base ** exponent) !== 8'd1) $display("FAIL zero exponent");
    base = 0;
    if ((base ** exponent) !== 8'd1) $display("FAIL zero to zero");
    base = 3;
    exponent = 6;
    wide_result = base ** exponent;
    narrow_result = base ** exponent;
    if (wide_result !== 16'd729 || narrow_result !== 4'd9) $display("FAIL context");
    base = 8'hff;
    large_exponent = 32'hffffffff;
    if ((base ** large_exponent) !== 8'hff) $display("FAIL large exponent");
    base = 8'bx0000001;
    exponent = 0;
    if ((base ** exponent) !== 8'bxxxxxxxx) $display("FAIL unknown base");
    base = 1;
    exponent = 4'bz001;
    if ((base ** exponent) !== 8'bxxxxxxxx) $display("FAIL unknown exponent");
    $display("PASS");
    $finish;
  end
// REFERENCE: 1fa5600785f83aa441d06638 independent-simulator 2026-10-12T07:58:22Z
endmodule
