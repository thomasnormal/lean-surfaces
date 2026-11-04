/* A zero-argument literal-return function is a pure value expression. */
module top;
  function bit [3:0] seven();
    return 4'd7;
  endfunction
  initial begin
    if (seven() == 4'd7)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
