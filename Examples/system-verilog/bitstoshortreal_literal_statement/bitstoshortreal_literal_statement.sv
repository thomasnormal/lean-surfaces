/*
:name: bitstoshortreal_literal_statement
:description: discarded literal $bitstoshortreal conversion is inert
:tags: 20.5
:type: simulation
*/
module top;
  initial begin
    $bitstoshortreal(32'h3fc0_0000);
    $display("PASS");
    $finish;
  end
endmodule
