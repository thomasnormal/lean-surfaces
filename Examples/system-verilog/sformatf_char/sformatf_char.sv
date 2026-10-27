/*
:name: sformatf_char
:description: §21.2.1.1 — literal integral %c formatting produces the low-byte ASCII character
:tags: 21.2.1.1,21.3.3
:type: simulation
*/
module top;
  initial begin
    $display("%s", $sformatf("%c", 8'h41));
    $finish;
  end
endmodule
