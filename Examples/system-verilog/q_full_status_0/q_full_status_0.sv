/*
:name: q_full_returns_0_when_not_full_v3
:description: §20.15.4 — $q_full returns 0 when queue is not full
:tags: 20.15.4
:type: simulation
*/
module top;
  int status;
  int full;
  initial begin
    $q_initialize(3, 1, 5, status);
    $q_add(3, 1, 100, status);
    $q_full(3, status);
    full = status;
    if (full == 0) $display("PASS");
    else $display("FAIL full=%0d", full);
    $finish;
  end
endmodule
