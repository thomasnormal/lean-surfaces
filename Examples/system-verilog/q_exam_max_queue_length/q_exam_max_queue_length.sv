/*
:name: q_exam_max_queue_length
:description: §20.15.5 Table 20-10 — $q_exam with q_stat_code=3 returns the maximum queue length reached since initialization
:tags: 20.15 20.15.5
:type: simulation
*/
module top;
  initial begin
    integer status, q_stat_val;
    $q_initialize(1, 1, 5, status); // FIFO, max 5
    $q_add(1, 10, 0, status);
    $q_add(1, 20, 0, status);
    $q_add(1, 30, 0, status);
    // q_stat_code=3 => maximum queue length reached
    $q_exam(1, 3, q_stat_val, status);
    if (status === 0 && q_stat_val === 3)
      $display("PASS");
    else
      $display("FAIL: status=%0d max_len=%0d", status, q_stat_val);
    $finish;
  end
endmodule
