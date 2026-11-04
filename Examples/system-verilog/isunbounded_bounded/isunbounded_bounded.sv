/* A bounded parameter is never the special unbounded value $. */
module top;
  parameter int max_cks = 5;
  initial begin
    if (!$isunbounded(max_cks))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
