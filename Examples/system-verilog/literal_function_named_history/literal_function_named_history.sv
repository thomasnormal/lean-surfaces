/* A literal-return function may receive a named literal-only input history. */
module top;
  bit selector;

  function automatic logic [3:0] seven(input logic ignored);
    return 4'd7;
  endfunction

  initial begin
    selector = 1'b0;
    if (seven(selector) == 4'd7)
      $display("PASS");
    else
      $display("FAIL first");
    selector = 1'b1;
    if (seven(selector) == 4'd7)
      $display("PASS");
    else
      $display("FAIL second");
    $finish;
  end
endmodule
