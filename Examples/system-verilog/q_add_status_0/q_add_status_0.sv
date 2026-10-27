/*
:name: q_add_status_0
:description: IEEE 1800-2023 20.15.2 — $q_add reports status 0 when an entry is added
:tags: 20.15 20.15.2
:type: simulation
*/
module top;
  integer status;
  initial begin
    $q_initialize(5, 1, 10, status);
    $q_add(5, 1, 100, status);
    if (status === 0)
      $display("PASS");
    else
      $display("FAIL: status=%0d", status);
    $finish;
  end
endmodule
