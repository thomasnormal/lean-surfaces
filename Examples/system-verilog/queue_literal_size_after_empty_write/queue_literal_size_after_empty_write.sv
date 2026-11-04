/* An empty queue assignment removes prior literal elements exactly. */
module top;
  int q[$] = {10, 20, 30};
  initial begin
    q = {};
    if (q.size() == 0)
      $display("PASS");
    else
      $display("FAIL");
  end
endmodule
