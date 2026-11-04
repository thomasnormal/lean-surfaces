/*
:name: literal_function_statement
:description: a discarded call to a zero-argument literal-return function is inert
:tags: 13.4
:type: simulation
*/
module top;
  function bit [3:0] seven();
    return 4'd7;
  endfunction

  initial begin
    seven();
    if (seven() == 4'd7)
      $display("PASS");
    else
      $display("FAIL");
  end
endmodule
