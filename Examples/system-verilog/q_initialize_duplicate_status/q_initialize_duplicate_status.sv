/*
:name: q_initialize_duplicate_status
:description: IEEE 1800-2023 20.15.6 — duplicate queue IDs report status 6
:tags: 20.15 20.15.6
:type: simulation
*/
module top;
  integer q_id, status;

  initial begin
    q_id = 1;
    $q_initialize(q_id, 1, 10, status);
    if (status !== 0) begin
      $display("FAIL: first status=%0d", status);
      $finish;
    end
    $q_initialize(q_id, 1, 10, status);
    if (status === 6)
      $display("PASS");
    else
      $display("FAIL: duplicate status=%0d", status);
    $finish;
  end
endmodule
