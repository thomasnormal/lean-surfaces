/* Source-pure real-to-integral casts round to nearest, ties away from zero. */
module top;
  real positive;
  real negative;
  int rounded;
  int tie_positive;
  int tie_negative;
  initial begin
    positive = 3.9;
    negative = -3.1;
    rounded = int'(positive);
    tie_positive = int'(2.5);
    tie_negative = int'(-2.5);
    if (rounded === 4 && tie_positive === 3 && tie_negative === -3)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
