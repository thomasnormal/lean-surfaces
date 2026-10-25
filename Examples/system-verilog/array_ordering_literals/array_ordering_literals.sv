/*
:name: array_ordering_literals
:description: IEEE 1800-2023 Section 7.12.2 -- finite literal dynamic arrays
  sort and reverse-sort through the flat-cell representation.
:tags: 7.12.2
:type: simulation
*/
module top;
  int ascending[];
  int descending[];

  initial begin
    ascending = new[4];
    descending = new[4];
    ascending[0] = 5;
    ascending[1] = -2;
    ascending[2] = 3;
    ascending[3] = 1;
    descending[0] = 5;
    descending[1] = -2;
    descending[2] = 3;
    descending[3] = 1;
    ascending.sort();
    descending.rsort();
    if (ascending[0] == -2 && ascending[1] == 1 &&
        ascending[2] == 3 && ascending[3] == 5 &&
        descending[0] == 5 && descending[1] == 3 &&
        descending[2] == 1 && descending[3] == -2)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
