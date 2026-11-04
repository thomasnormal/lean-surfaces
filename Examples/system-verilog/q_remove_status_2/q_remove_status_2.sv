/*
:name: q_remove_status_2
:description: IEEE 1800-2023 20.15.6 — undefined queue IDs report status 2
:tags: 20.15 20.15.6
:type: simulation
*/
module top;
  integer status, job, info;
  initial begin
    $q_remove(999, job, info, status);
    if (status === 2)
      $display("PASS");
    else
      $display("FAIL: status=%0d", status);
    $finish;
  end
endmodule
