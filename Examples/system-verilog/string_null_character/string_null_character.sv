/*
:name: string_null_character
:description: §6.16 — assigning integral zero to a string byte is ignored
:tags: 6.16 string character assignment
:type: simulation
*/
module top;
  string s;

  initial begin
    s = "hello";
    s[1] = 0;
    if (s == "hello") begin
      $display("PASS");
    end
    else begin
      $display("FAIL: assigning 0 to string char should be ignored");
    end
    $finish;
  end
endmodule
