/*
:name: literal_format_concat
:description: §21.2 — a display format may be a concatenation of string literals
:tags: 21.2
:type: simulation
*/
module top;
  initial begin
    // PASS
    $display({"PA", "SS"});
    $finish;
  end
endmodule
