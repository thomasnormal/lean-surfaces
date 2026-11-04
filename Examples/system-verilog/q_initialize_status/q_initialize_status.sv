/*
:name: q_initialize_status
:description: IEEE 1800-2023 20.15.6 — unsupported queue type reports status 4
:tags: 20.15 20.15.6
:type: simulation
*/
module top;
  integer status;

  initial begin
    $q_initialize(20, 99, 10, status);
    if (status === 4)
      $display("PASS");
    else
      $display("FAIL: status=%0d", status);
    $finish;
  end
endmodule
