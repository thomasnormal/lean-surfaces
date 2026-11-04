/*
:name: dynamic_fixed_array_copy
:description: IEEE 1800-2023 Section 7.6 -- a constant-size 2-state dynamic
  array can be copied into a same-sized fixed unpacked array.
:tags: 7.6
:type: simulation
*/
module top;
  int fixed_values[5];
  int dynamic_values[] = new[5];
  initial begin
    for (int i = 0; i < 5; i++) dynamic_values[i] = i + 100;
    fixed_values = dynamic_values;
    if (fixed_values[0] == 100 && fixed_values[4] == 104)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
