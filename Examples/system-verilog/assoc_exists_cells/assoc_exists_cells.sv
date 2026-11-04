/* Literal associative-array value cells carry exact exists(key) presence. */
module top;
  initial begin
    int score[string];
    logic [7:0] code[int];
    if (score.exists("answer") || code.exists(7)) begin
      $display("FAIL: empty arrays report a key");
      $finish;
    end
    score["answer"] = 40;
    code[7] = 8'hA5;
    score["answer"] += 2;
    if (score.exists("answer") && code.exists(7) &&
        score["answer"] == 42 && code[7] === 8'hA5)
      $display("PASS");
    else
      $display("FAIL: finite associative cells");
    $finish;
  end
endmodule
