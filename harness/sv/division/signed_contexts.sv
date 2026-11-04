module top;
  logic signed [3:0] negative, positive, minimum_value, minus_one, overflow;
  logic [3:0] unsigned_value;
  logic signed [7:0] signed_quotient, both_negative;
  logic [7:0] mixed_quotient;
  initial begin
    negative = -4'sd7;
    positive = 4'sd3;
    unsigned_value = 4'd3;
    minimum_value = 4'sb1000;
    minus_one = -4'sd1;
    signed_quotient = negative / positive;
    both_negative = negative / -positive;
    mixed_quotient = negative / unsigned_value;
    overflow = minimum_value / minus_one;
    if ((signed_quotient === 8'hfe) && (both_negative === 8'h02) &&
        (mixed_quotient === 8'h03) && (overflow === 4'h8))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: dbe496aa623e770def7e2813 independent-simulator 2026-10-11T19:29:37Z
