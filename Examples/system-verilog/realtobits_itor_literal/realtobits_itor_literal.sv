/*
:name: realtobits_itor_literal
:description: exact IEEE bits for a literal integer-to-real conversion
:tags: 20.5 20.8.1
:type: simulation
*/
module top;
  initial begin
    if ($realtobits($itor(-17)) === 64'hc031_0000_0000_0000)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
