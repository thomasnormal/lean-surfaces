/*
:name: dynamic_array_new_pattern
:description: IEEE 1800-2023 Section 7.5.1 -- a finite scalar dynamic-array
  allocation initialized by an exact positional assignment pattern.
:tags: 7.5.1 10.9
:type: simulation
*/
module top;
  initial begin
    int values[];
    logic bits[];
    values = new[3]('{10, 20, 30});
    bits = new[3]('{1'bx, 1'b1, 1'bz});
    if (values.size() == 3 && values[0] == 10 && values[1] == 20 &&
        values[2] == 30 && bits.size() == 3 && bits[0] === 1'bx &&
        bits[1] === 1'b1 && bits[2] === 1'bz)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
