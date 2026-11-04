/*
:name: dynamic_array_four_state
:description: IEEE 1800-2023 Section 7.5 -- a finite four-state dynamic
  array allocation supplies x defaults and supports indexed writes.
:tags: 7.5
:type: simulation
*/
module top;
  logic values[];
  int index;

  initial begin
    values = new[3];
    index = 2;
    values[index] = 1'b1;
    if (values[0] === 1'bx && values[index] === 1'b1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
