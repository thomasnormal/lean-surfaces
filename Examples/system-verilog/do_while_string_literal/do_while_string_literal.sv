/*
:name: do_while_string_literal
:description: a pure literal write to an opaque string can be erased before a do-while
:tags: 12.7.5
:type: simulation
*/
module top;
  initial begin
    int count;
    string s;
    s = "abc";
    count = 0;
    do begin
      count++;
    end while (count < 3 && count != 100);
    if (count == 3) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
