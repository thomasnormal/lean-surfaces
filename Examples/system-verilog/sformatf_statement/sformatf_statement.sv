/*
:name: sformatf_statement
:description: §21.3.3 — a discarded literal $sformatf call has no modeled state effect
:tags: 21.2.1.1,21.3.3
:type: simulation
*/
module top;
  initial begin
    $sformatf("%H", 8'hAB);
    $sformatf("%b", 4'b1010);
    $display("PASS");
    $finish;
  end
endmodule
