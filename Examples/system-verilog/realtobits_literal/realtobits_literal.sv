/*
:name: realtobits_literal
:description: literal $realtobits conversions use IEEE-754 bit patterns
:tags: 20.5
:type: simulation
*/
module top;
  initial begin
    $realtobits(1.0);
    if ($realtobits(-2.5) === 64'hc004_0000_0000_0000)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
