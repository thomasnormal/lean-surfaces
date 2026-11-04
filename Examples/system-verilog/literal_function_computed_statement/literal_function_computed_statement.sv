/*
:name: literal_function_computed_statement
:description: A discarded literal-return function call may receive a pure integral expression
:tags: 13.4
:type: simulation
*/
module top;
  function bit [3:0] seven(input bit selector);
    return 4'd7;
  endfunction

  initial begin
    seven(1'b1 + 1'b0);
    if (seven(2'b10 ^ 2'b11) == 4'd7)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
