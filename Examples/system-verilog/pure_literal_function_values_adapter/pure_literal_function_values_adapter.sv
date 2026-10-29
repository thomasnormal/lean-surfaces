/*
:name: pure_literal_function_values_adapter
:description: Pure literal-return function calls carry no adapter state.
:tags: 13.4
:type: simulation
*/
module top;
  function bit [3:0] seven(input bit selector);
    return 4'd7;
  endfunction
  function bit [3:0] zero();
  endfunction
  initial begin
    seven(1'b0);
    if (seven(1'b1) == 4'd7 && zero() == 4'd0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
