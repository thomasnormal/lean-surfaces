/*
:name: shortrealtobits_itor_literal
:description: exact IEEE single bits for a literal integer-to-real conversion
:tags: 20.5 20.8.2
:type: simulation
*/
module top;
  initial begin
    if ($shortrealtobits($itor(-17)) === 32'hc188_0000)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
