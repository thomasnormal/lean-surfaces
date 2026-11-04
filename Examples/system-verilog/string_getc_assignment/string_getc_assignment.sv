/* A direct blocking literal write supplies the source-pure string history. */
module top;
  string s;
  byte negative;
  byte out_of_range;
  byte first;
  byte latest;
  initial begin
    s = "hello";
    negative = s.getc(-1);
    out_of_range = s.getc(100);
    first = s.getc(0);
    s = "X";
    latest = s.getc(0);
    if (negative === 0 && out_of_range === 0 && first === 8'h68 &&
        latest === 8'h58)
      $display("PASS");
    else
      $display("FAIL: getc assignment history");
    $finish;
  end
endmodule
