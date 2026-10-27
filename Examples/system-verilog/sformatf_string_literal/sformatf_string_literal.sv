/*
:name: sformatf_string_literal
:description: §21.2.1.1 — a literal ASCII string is a pure %s formatting operand
:tags: 21.2.1.1,21.3.3
:type: simulation
*/
module top;
  // expected self-check output: hello
  initial begin
    $display("%s", $sformatf("%s", "hello"));
    $finish;
  end
endmodule
