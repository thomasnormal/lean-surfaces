module top;
  logic signed [7:0] base;
  logic signed [3:0] exponent;
  logic [3:0] unsigned_exponent;
  logic signed [15:0] wide_result;
  initial begin
    base = -3;
    exponent = 3;
    if ((base ** exponent) !== -8'sd27) $display("FAIL negative base");
    base = -1;
    if ((base ** exponent) !== -8'sd1) $display("FAIL negative odd");
    exponent = -2;
    if ((base ** exponent) !== 8'sd1) $display("FAIL negative even");
    base = 1;
    if ((base ** exponent) !== 8'sd1) $display("FAIL one reciprocal");
    base = -2;
    unsigned_exponent = 3;
    wide_result = base ** unsigned_exponent;
    if (wide_result !== -16'sd8) $display("FAIL signed base unsigned exponent");
    base = -128;
    exponent = 2;
    wide_result = (-base) ** exponent;
    if (wide_result !== 16'sd16384) $display("FAIL context before negation");
    $display("PASS");
    $finish;
  end
// REFERENCE: 0a2ee5cdf62683b5a43ef7b6 independent-simulator 2026-10-12T09:34:04Z
endmodule
