/*
:name: string_sformatf_binary_assignment
:description: §21.2.1.1 — literal integral binary formatting assigns to strings
:tags: 21.2.1.1 21.3.3
:type: simulation
*/
module top;
  string lower, upper;
  initial begin
    lower = $sformatf("%b", 8'b00001010);
    upper = $sformatf("%B", 4'b1010);
    if (lower == "00001010" && upper == "1010") $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
