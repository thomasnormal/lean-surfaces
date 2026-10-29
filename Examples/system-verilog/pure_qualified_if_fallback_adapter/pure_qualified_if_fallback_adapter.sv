/*
:name: pure_qualified_if_fallback_adapter
:description: Unique and priority if chains with explicit fallbacks lower as ordinary adapter control.
:tags: 12.4.2
:type: simulation
*/
module top;
  int value;
  int result;
  initial begin
    value = 2;
    result = 0;
    unique if (value == 1)
      result = 1;
    else if (value == 2)
      result = 2;
    else
      result = 99;
    priority if (value > 3)
      result = 3;
    else
      result = 4;
    if (result == 4)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
