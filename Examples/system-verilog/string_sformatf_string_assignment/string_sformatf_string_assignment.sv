/*
:name: string_sformatf_string_assignment
:description: §21.2.1.1 — source-pure string $sformatf results assign to strings
:tags: 21.2.1.1 21.3.3
:type: simulation
*/
module top;
  string source, lower, upper;
  initial begin
    source = "Hello";
    lower = $sformatf("%s", source);
    upper = $sformatf("%S", "World");
    if (lower == "Hello" && upper == "World") $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
