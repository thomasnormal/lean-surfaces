/*
:name: bitstoreal_literal_statement
:description: discarded literal $bitstoreal conversion is inert
:tags: 20.5
:type: simulation
*/
module top;
  initial begin
    $bitstoreal(64'h3ff8_0000_0000_0000);
    $display("PASS");
    $finish;
  end
endmodule
