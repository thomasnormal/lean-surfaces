/*
:name: large_fixed_array
:description: a large fixed unpacked array admits sparse constant-index cells
:tags: 7.4.2
:type: simulation
*/
module top;
  bit value [0:16777215];
  initial begin
    value[0] = 1'b1;
    value[16777215] = 1'b1;
    if (value[0] === 1'b1 && value[16777215] === 1'b1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
