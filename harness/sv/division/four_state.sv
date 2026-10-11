module top;
  logic [3:0] numerator, denominator, quotient;
  logic [7:0] wide;
  bit [3:0] two_state;
  initial begin
    numerator = 4'b0111;
    denominator = 4'b0000;
    quotient = numerator / denominator;
    wide = numerator / denominator;
    two_state = numerator / denominator;
    if ((quotient !== 4'bxxxx) || (wide !== 8'bxxxxxxxx) ||
        (two_state !== 4'b0000))
      $display("FAIL");
    else begin
      numerator = 4'b0000;
      denominator = 4'b0x01;
      quotient = numerator / denominator;
      if (quotient !== 4'bxxxx)
        $display("FAIL");
      else begin
        numerator = 4'b01z1;
        denominator = 4'b0011;
        quotient = numerator / denominator;
        if (quotient === 4'bxxxx)
          $display("PASS");
        else
          $display("FAIL");
      end
    end
    $finish;
  end
endmodule
// REFERENCE: a9f75c4223e0ed672e493540 independent-simulator 2026-10-11T19:29:34Z
