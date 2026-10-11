module top;
  logic [7:0] quotient, factor;
  logic signed [7:0] signed_quotient, signed_factor, mixed_quotient;
  initial begin
    quotient = 8'd255;
    factor = 8'd3;
    quotient /= factor;
    signed_quotient = -8'sd13;
    signed_factor = 8'sd5;
    signed_quotient /= signed_factor;
    factor = 8'd5;
    mixed_quotient = -8'sd13;
    mixed_quotient /= factor;
    if ((quotient === 8'h55) && (signed_quotient === 8'hfe) &&
        (mixed_quotient === 8'h30))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 8271e7c710f891f3573ec629 independent-simulator 2026-10-11T19:29:32Z
