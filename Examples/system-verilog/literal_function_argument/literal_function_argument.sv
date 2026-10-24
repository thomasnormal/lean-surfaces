/* A pure literal-return function may receive literal input arguments. */
module top;
  function automatic logic [3:0] seven(input logic selector);
    return 4'd7;
  endfunction
  initial begin
    if (seven(1'b0) == 4'd7)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
