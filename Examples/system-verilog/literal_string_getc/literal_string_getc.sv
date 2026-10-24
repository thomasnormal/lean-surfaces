module top;
  string s = "abc";
  initial begin
    int a = s.getc(10);
    int b = s.getc(-1);
    int c = s.getc(0);
    if (a == 0 && b == 0 && c == 8'h61) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
