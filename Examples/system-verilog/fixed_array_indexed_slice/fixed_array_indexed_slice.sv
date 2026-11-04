/*
:name: fixed_array_indexed_slice
:description: §7.4.6 — runtime indexed slices of bounded unpacked arrays
:tags: 7.4.6
:type: simulation
*/
module top;
  int A[4];
  int B[4];
  int i, j;
  parameter int c = 2;
  initial begin
    for (int k = 0; k < 4; k++) B[k] = k + 1;
    i = 1; j = 2;
    A[i+:c] = B[j+:c];
    if (A[1] === 3 && A[2] === 4)
      $display("PASS");
    else
      $display("FAIL");
  end
endmodule
