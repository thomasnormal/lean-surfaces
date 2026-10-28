/*
:name: queue_literal_then_empty_concat
:description: IEEE 1800-2023 Section 10.10 -- a literal queue write
  followed by an empty queue concatenation leaves size zero.
:tags: 7.10 10.10
:type: simulation
*/
module top;
  int q[$];
  initial begin
    q = {1, 2, 3};
    q = {};
    if (q.size() == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
