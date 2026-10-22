/*
:name: fixed_array_packed_leaf_2state
:description: IEEE 1800-2023 Sections 7.4 and 7.4.4 -- bounded unpacked
  cells may have a multidimensional packed integral leaf.
:tags: 7.4.4
:type: simulation
*/
module top;
  bit [1:0][3:0] values[0:1];

  initial begin
    values[0] = 8'hA5;
    if (values[0] === 8'hA5 && values[1] === 8'b0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
