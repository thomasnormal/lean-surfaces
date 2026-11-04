/* Finite literal integral-key associative-array cells use the flat state. */
module top;
  logic [7:0] score[int];

  initial begin
    score[-1] = 8'h5A;
    score[2] = 8'hA5;
    if (score[-1] === 8'h5A && score[2] === 8'hA5)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
