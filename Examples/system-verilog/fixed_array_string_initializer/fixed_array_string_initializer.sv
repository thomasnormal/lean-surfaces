/* A string literal initializes fixed unpacked byte cells in declared order. */
module top;
  byte text[3:0] = "hi2";

  initial begin
    if (text[3] != "h") $finish;
    if (text[2] != "i") $finish;
    if (text[1] != "2") $finish;
    if (text[0] != 0) $finish;
    $display("PASS");
    $finish;
  end
endmodule
