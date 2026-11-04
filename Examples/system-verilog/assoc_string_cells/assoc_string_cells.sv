/* Finite literal string-key associative-array cells use the flat state. */
module top;
  initial begin
    int score[string];
    logic [7:0] tag[string];
    score["alice"] = 95;
    score["bob"] = 87;
    tag[""] = 8'hA5;
    tag["x"] = 8'b10xz_01zx;
    if (score["alice"] === 95 && score["bob"] === 87 &&
        tag[""] === 8'hA5 && tag["x"] === 8'b10xz_01zx)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
