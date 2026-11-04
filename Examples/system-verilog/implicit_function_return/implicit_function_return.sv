/* Pure literal assignments to implicit function return variables. */
module top;
  function f;
    f = 1'b1;
  endfunction
  function int g();
    g = 1;
  endfunction
  initial begin
    if (f() === 1'b1)
      $display("PASS");
    else
      $display("FAIL");
    g();
    $display("PASS2");
    $finish;
  end
endmodule
