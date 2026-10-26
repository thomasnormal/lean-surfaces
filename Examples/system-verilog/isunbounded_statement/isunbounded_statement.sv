/* A discarded bounded $isunbounded query is a pure zero-bit result. */
module top;
  parameter int max_cks = 5;
  initial begin
    $isunbounded(5);
    $isunbounded(max_cks);
    $display("PASS");
    $finish;
  end
endmodule
