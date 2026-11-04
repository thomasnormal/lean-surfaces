module top;
  // dynamic abab
  string text;
  string repeated;
  initial begin
    text = "ab";
    repeated = {2{text}};
    $display("dynamic %s", repeated);
    $finish;
  end
endmodule
