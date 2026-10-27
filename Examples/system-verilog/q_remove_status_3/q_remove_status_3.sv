/*
:name: q_remove_status_3
:description: IEEE 1800-2023 20.15.6 — removing from an empty queue reports status 3
:tags: 20.15 20.15.6
:type: simulation
*/
module top;
  integer q_id, status, job, info;
  initial begin
    q_id = 1;
    $q_initialize(q_id, 1, 10, status);
    if (status !== 0) begin
      $display("FAIL: init status=%0d", status);
      $finish;
    end
    $q_remove(q_id, job, info, status);
    if (status === 3)
      $display("PASS");
    else
      $display("FAIL: status=%0d", status);
    $finish;
  end
endmodule
