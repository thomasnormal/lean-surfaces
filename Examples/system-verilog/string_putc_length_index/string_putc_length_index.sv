/*
:name: string_putc_length_index
:description: IEEE 1800-2023 §6.16.2 - string.putc() at str.len() is an unchanged out-of-range write.
:tags: 6.16 6.16.2 string putc
:type: simulation
*/
module top;
  initial begin
    string s = "abc";
    s.putc(s.len(), "X");
    if (s == "abc")
      $display("PASS");
    else
      $display("FAIL: s='%s'", s);
    $finish;
  end
endmodule
