/*
:name: fixed_array_disjoint_subarray_copy
:description: IEEE 1800-2023 Section 7.6 -- a blocking copy between
  disjoint constant subarrays snapshots one fixed-array row before writing.
:tags: 7.6 10.10
:type: simulation
*/
module top;
  int value [0:1][0:2];
  initial begin
    value[0] = '{1, 2, 3};
    value[1] = '{4, 5, 6};
    value[0] = value[1];
    if (value[0][0] == 4 && value[0][1] == 5 && value[0][2] == 6 &&
        value[1][0] == 4 && value[1][2] == 6)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
