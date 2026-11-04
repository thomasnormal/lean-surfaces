/*
:name: dynamic_array_self_resize
:description: IEEE 1800-2023 Section 7.5.1 -- a finite scalar dynamic array
  grows from new[3] to new[5](self), preserving old cells and padding zeros.
:tags: 7.5.1
:type: simulation
*/
module top;
  initial begin
    int values[];
    values = new[3];
    values[0] = 4;
    values[1] = 5;
    values[2] = 6;
    values = new[5](values);
    if (values[0] == 4 && values[1] == 5 && values[2] == 6 &&
        values[3] == 0 && values[4] == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
