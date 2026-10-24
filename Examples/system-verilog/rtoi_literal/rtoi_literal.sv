/*
:name: rtoi_literal
:description: literal $rtoi conversions truncate toward zero
:tags: 20.5
:type: simulation
*/
module top;
  initial begin
    $rtoi(0.5);
    if ($rtoi(123.9) === 123 && $rtoi(-2.7) === -2)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
