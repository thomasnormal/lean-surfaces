/*
:name: string_sformatf_literal_assignment
:description: §21.2.1.1 — literal hexadecimal $sformatf results assign to strings
:tags: 21.2.1.1 21.3.3
:type: simulation
*/
module top;
  string lower, upper;
  initial begin
    lower = $sformatf("%h", 32'hDEAD_BEEF);
    upper = $sformatf("%H", 32'hDEAD_BEEF);
    if (lower == upper) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
