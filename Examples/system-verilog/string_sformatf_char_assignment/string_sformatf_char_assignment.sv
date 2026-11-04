/*
:name: string_sformatf_char_assignment
:description: §21.2.1.1 — literal integral character formatting assigns to strings
:tags: 21.2.1.1 21.3.3
:type: simulation
*/
module top;
  string lower, upper;
  initial begin
    lower = $sformatf("%c", 8'h41);
    upper = $sformatf("%C", 8'h42);
    if (lower == "A" && upper == "B") $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
