/*
:name: string_sformatf_octal_assignment
:description: §21.2.1.1 — literal integral octal formatting assigns to strings
:tags: 21.2.1.1 21.3.3
:type: simulation
*/
module top;
  string lower, upper;
  initial begin
    lower = $sformatf("%o", 8'h0A);
    upper = $sformatf("%O", 4'b1010);
    if (lower == "12" && upper == "12") $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
