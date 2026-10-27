/*
:name: bits_fixed_expr
:description: IEEE 1800-2023 §20.6.2 — $bits reads a fixed expression's type without evaluating it
:tags: 20.6 20.6.2
:type: simulation
*/
module top;
  logic [7:0] value = 8'hA5;
  initial begin
    if ($bits(value++) == 8 && value === 8'hA5)
      $display("PASS");
    else
      $display("FAIL: bits=%0d value=%h", $bits(value++), value);
    $finish;
  end
endmodule
