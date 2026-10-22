/*
:name: fixed_array_2state
:description: bounded multidimensional two-state arrays flatten to independent cells
:tags: 6.8,7.4.2
:type: simulation
*/
module top;
  bit [3:0] matrix[2][3];
  initial begin
    matrix[1][2] = 4'ha;
    if (matrix[1][2] == 4'ha && matrix[0][0] == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
