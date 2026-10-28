/*
:name: string_sformatf_zero_width_string_assignment
:description: §21.2.1.2 — zero-width string formatting assigns exact text to strings
:tags: 21.2.1.2 21.2.1.7 21.3.3
:type: simulation
*/
module top;
  string exact, wrapped;
  initial begin
    exact = $sformatf("%0s", "abc");
    wrapped = $sformatf("<%0S>", "World");
    if (exact == "abc" && wrapped == "<World>") $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
