/*
:name: itor_literal_statement
:description: discarded literal $itor conversion is inert
:tags: 20.5
:type: simulation
*/
module top;
  initial begin
    $itor(-17);
    $display("PASS");
    $finish;
  end
endmodule
