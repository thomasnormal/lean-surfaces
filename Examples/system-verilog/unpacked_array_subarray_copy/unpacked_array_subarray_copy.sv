/*
:name: unpacked_array_subarray_copy
:description: IEEE 1800-2023 7.4.4 — constant subarray selection copies a row cellwise
:tags: 7.4.4
:type: simulation
*/
module top;
  int source [0:1][0:2] = '{'{10, 20, 30}, '{40, 50, 60}};
  int row [0:2];
  int patterned [0:1][0:2];
  initial begin
    row = source[1];
    if (row[0] == 40 && row[1] == 50 && row[2] == 60)
      $display("PASS");
    else
      $display("FAIL");
    patterned[0] = '{1, 2, 3};
    if (patterned[0][0] == 1 && patterned[0][1] == 2 && patterned[0][2] == 3)
      $display("PASS2");
    else
      $display("FAIL2");
    $finish;
  end
endmodule
