/*
:name: fixed_array_subarray_self_copy
:description: IEEE 1800-2023 Section 7.6 -- an exact blocking self-copy
  of one fixed-array row is a no-op.
:tags: 7.6 10.10
:type: simulation
*/
module top;
  int value [0:1][0:2];
  initial begin
    value[0] = '{1, 2, 3};
    value[0] = value[0];
    if (value[0][0] == 1 && value[0][1] == 2 && value[0][2] == 3)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
