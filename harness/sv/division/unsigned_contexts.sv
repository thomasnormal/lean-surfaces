module top;
  logic [7:0] numerator, denominator, quotient, negative_bits;
  logic [3:0] narrow;
  logic [15:0] wide;
  initial begin
    numerator = 8'd250;
    denominator = 8'd3;
    quotient = numerator / denominator;
    narrow = numerator / denominator;
    wide = numerator / denominator;
    negative_bits = -8'sd1 / 8'd2;
    if ((quotient === 8'h53) && (narrow === 4'h3) &&
        (wide === 16'h0053) && (negative_bits === 8'h7f))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 1599f8c2724eab6d9b113bd2 independent-simulator 2026-10-11T19:29:40Z
