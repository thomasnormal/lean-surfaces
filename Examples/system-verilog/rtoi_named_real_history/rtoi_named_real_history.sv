/* A source-pure named real history can feed exact $rtoi conversion. */
module top;
  real positive;
  real negative;
  initial begin
    positive = 123.9;
    negative = -2.7;
    if ($rtoi(positive) === 123 && $rtoi(negative) === -2)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
