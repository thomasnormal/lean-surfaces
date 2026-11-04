/*
:name: fixed_array_nested_subarray_copy
:description: §7.4.4 — constant nested subarray reference copied by ordinal cell
:tags: 7.4.4, 7.6
:type: simulation
*/
module top;
  logic [7:0] source [0:1][0:3][0:1];
  logic [7:0] target [4:7][9:10];

  initial begin
    source[1][0][0] = 8'h11;
    source[1][0][1] = 8'h12;
    source[1][1][0] = 8'h21;
    source[1][1][1] = 8'h22;
    source[1][2][0] = 8'h31;
    source[1][2][1] = 8'h32;
    source[1][3][0] = 8'h41;
    source[1][3][1] = 8'h42;
    target = source[1];
    if (target[4][9] == 8'h11 && target[4][10] == 8'h12 &&
        target[5][9] == 8'h21 && target[5][10] == 8'h22 &&
        target[6][9] == 8'h31 && target[6][10] == 8'h32 &&
        target[7][9] == 8'h41 && target[7][10] == 8'h42)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
