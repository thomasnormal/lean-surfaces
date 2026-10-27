/* Dynamic associative-array keys stay outside finite flat-cell storage. */
module top;
  initial begin
    logic [7:0] score[string];
    string key;
    key = "answer";
    score[key] = 42;
    if (score.exists(key)) $display("PASS");
    $finish;
  end
endmodule
