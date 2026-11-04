/*
:name: string_null_literal_character
:description: §6.16 — assigning the NUL string literal to a string byte is ignored
:tags: 6.16 string character assignment
:type: simulation
*/
module top;
  string s = "abc";
  initial begin
    s[1] = "\0";
    if (s == "abc") $display("PASS");
    else $display("FAIL: NUL string byte changed the string");
    $finish;
  end
endmodule
