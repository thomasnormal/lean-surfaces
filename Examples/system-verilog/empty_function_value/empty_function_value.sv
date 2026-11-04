/* An empty function's declared return type supplies its default value. */
module top;
  function bit [3:0] zero();
  endfunction
  function logic [3:0] unknown();
  endfunction
  initial begin
    if (zero() == 4'b0000 && unknown() === 4'bxxxx)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
