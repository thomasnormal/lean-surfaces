/*
:name: queue_empty_init
:description: §7.10 — uninitialized queue starts empty; {} denotes empty queue
:tags: 7.10
:type: simulation
*/
module top;
  int q1[$];
  int q2[$] = {};
  initial begin
    if (q1.size() == 0 && q2.size() == 0)
      $display("PASS");
    else
      $display("FAIL: q1.size=%0d q2.size=%0d", q1.size(), q2.size());
    $finish;
  end
endmodule
