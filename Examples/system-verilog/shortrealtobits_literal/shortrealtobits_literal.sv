/*
:name: shortrealtobits_literal
:description: literal $shortrealtobits conversions use IEEE single bits
:tags: 20.5
:type: simulation
*/
module top;
  initial begin
    $shortrealtobits(1.0);
    if ($shortrealtobits(-2.5) === 32'hc020_0000)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
