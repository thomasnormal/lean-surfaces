/*
:name: q_add_status_1_when_full
:description: IEEE 1800-2023 20.15.2 — $q_add reports status 1 when the queue is full
:tags: 20.15 20.15.2 20.15.6
:type: simulation
*/
module top;
  integer status;
  initial begin
    $q_initialize(5, 1, 2, status);
    $q_add(5, 1, 0, status);
    $q_add(5, 2, 0, status);
    $q_add(5, 3, 0, status);
    if (status === 1)
      $display("PASS");
    else
      $display("FAIL: expected status=1 (full), got %0d", status);
    $finish;
  end
endmodule
