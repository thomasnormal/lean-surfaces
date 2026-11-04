/*
:name: array_reverse
:description: IEEE 1800-2023 7.12.2 — reverse a literal fixed unpacked array in place
:tags: 7.12.2
:type: simulation
*/
module top;
  int values[5] = '{1, 2, 3, 4, 5};

  initial begin
    values.reverse();
    if (values[0] == 5 && values[1] == 4 && values[2] == 3 &&
        values[3] == 2 && values[4] == 1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
