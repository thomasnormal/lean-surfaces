/*
:name: sformatf_string_history
:description: §21.2.1.1 — a source-pure ASCII string history is a %s operand
:tags: 21.2.1.1,21.3.3
:type: simulation
*/
module top;
  string s;
  initial begin
    s = "hello";
    $display("%s", $sformatf("%s", s));
    $finish;
  end
endmodule
