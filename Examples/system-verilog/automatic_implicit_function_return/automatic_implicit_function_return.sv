/* Pure literal assignments to automatic implicit function return variables. */
module top;
  function automatic f;
    f = 1'b1;
  endfunction
  function automatic int g();
    g = 2;
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
