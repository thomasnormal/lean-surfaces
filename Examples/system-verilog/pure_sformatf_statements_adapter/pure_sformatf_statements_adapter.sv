/*
:name: pure_sformatf_statements_adapter
:description: Discarded literal $sformatf results carry no adapter state.
:tags: 21.3.3
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
