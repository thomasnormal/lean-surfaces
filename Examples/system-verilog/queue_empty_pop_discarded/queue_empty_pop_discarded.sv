/* Discarding an empty queue pop is an observable no-op. */
module top;
  int q[$];
  initial begin
    void'(q.pop_front());
    void'(q.pop_back());
    if (q.size() === 0)
      $display("PASS");
    else
      $display("FAIL: discarded empty pop changed queue");
    $finish;
  end
endmodule
