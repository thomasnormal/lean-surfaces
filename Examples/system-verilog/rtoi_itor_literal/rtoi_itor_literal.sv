/*
:name: rtoi_itor_literal
:description: $rtoi of an exact literal $itor conversion
:tags: 20.8.1 20.8.2
:type: simulation
*/
module top;
  integer value;
  initial begin
    value = $rtoi($itor(-17));
    if (value === -17)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
