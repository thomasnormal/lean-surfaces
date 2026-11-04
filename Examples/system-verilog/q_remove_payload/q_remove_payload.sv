/*
:name: q_remove_payload
:description: IEEE 1800-2023 20.15.3 — a literal FIFO queue returns the added job and inform values
:tags: 20.15 20.15.2 20.15.3
:type: simulation
*/
module top;
  integer status;
  integer job;
  integer info;
  initial begin
    $q_initialize(2, 1, 10, status);
    $q_add(2, 42, 99, status);
    $q_remove(2, job, info, status);
    if (status === 0 && job === 42 && info === 99)
      $display("PASS");
    else
      $display("FAIL: status=%0d job=%0d info=%0d", status, job, info);
    $finish;
  end
endmodule
