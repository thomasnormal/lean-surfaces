/* A literal-only queue initializer fixes the exact size query. */
module top;
  int q[$] = {10, 20, 30};
  initial begin
    if (q.size() == 3)
      $display("PASS");
    else
      $display("FAIL");
  end
endmodule
