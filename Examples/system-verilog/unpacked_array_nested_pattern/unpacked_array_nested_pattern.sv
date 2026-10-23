/*
:name: unpacked_array_nested_pattern
:description: IEEE 1800-2023 10.9.1 — nested fixed-array assignment pattern replication
:tags: 10.9.1
:type: simulation
*/
module top;
  int value [0:1][0:2];
  initial begin
    value = '{2{'{3{7}}}};
    if (value[0][0] == 7 && value[0][1] == 7 && value[0][2] == 7 &&
        value[1][0] == 7 && value[1][1] == 7 && value[1][2] == 7)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
