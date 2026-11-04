/*
:name: fixed_array_pattern_2state
:description: IEEE 1800-2023 Section 10.9.1 -- nested replication in an
  assignment pattern initializes a bounded two-state unpacked array.
:tags: 10.9.1
:type: simulation
*/
module top;
  int values[1:2][1:3] = '{2{'{3{5}}}};

  initial begin
    if (values[1][1] == 5 && values[1][3] == 5 &&
        values[2][1] == 5 && values[2][3] == 5)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
