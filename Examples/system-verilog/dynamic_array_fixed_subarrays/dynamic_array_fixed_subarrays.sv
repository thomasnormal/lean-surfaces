/*
:name: dynamic_array_fixed_subarrays
:description: IEEE 1800-2023 Section 7.5.1 -- a dynamic outer array with
  finite fixed unpacked integral subarrays is flattened into scalar cells.
:tags: 7.5.1
:type: simulation
*/
module top;
  bit [3:0] rows[][2];
  int cube[][2][3];

  initial begin
    rows = new[3];
    cube = new[2];
    rows[0][0] = 4'ha;
    rows[2][1] = 4'h5;
    cube[1][0][2] = 42;
    if (rows.size() == 3 && rows[0][0] == 4'ha && rows[2][1] == 4'h5 &&
        rows[1][0] == 4'h0 && cube.size() == 2 && cube[1][0][2] == 42 &&
        cube[0][1][1] == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
