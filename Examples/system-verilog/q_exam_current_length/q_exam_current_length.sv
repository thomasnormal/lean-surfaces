/*
:name: q_exam_current_length
:description: §20.15.5 — $q_exam with q_stat_code=1 returns the current queue length in q_stat_value
:tags: 20.15 20.15.5
:type: simulation
*/
module top;
  initial begin
    integer status, q_stat_val;
    $q_initialize(1, 1, 10, status); // FIFO, max 10
    $q_add(1, 10, 0, status);
    $q_add(1, 20, 0, status);
    // q_stat_code=1 => current queue length
    $q_exam(1, 1, q_stat_val, status);
    if (status === 0 && q_stat_val === 2)
      $display("PASS");
    else
      $display("FAIL: status=%0d len=%0d", status, q_stat_val);
    $finish;
  end
endmodule
