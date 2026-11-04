/*
:name: packed_array_dynamic_wide_slice
:description: §11.5.1 — dynamic indexed slices over nested packed elements
:tags: 7.4.6 11.5.1
:type: simulation
*/
module top;
  logic [1:0][3:0] desc;
  logic [0:1][3:0] asc;
  int i;

  initial begin
    desc = 8'hAB;
    i = 0;
    if (desc[i +: 2] !== 8'hAB)
      $display("FAIL");
    desc[i +: 2] = 8'hCD;
    if (desc !== 8'hCD)
      $display("FAIL");
    desc = 8'hAB;
    i = 1;
    if (desc[i -: 2] !== 8'hAB)
      $display("FAIL");
    desc[i -: 2] = 8'hEF;
    if (desc !== 8'hEF)
      $display("FAIL");
    asc = 8'hAB;
    i = 0;
    if (asc[i +: 2] !== 8'hAB)
      $display("FAIL");
    asc[i +: 2] = 8'h12;
    if (asc !== 8'h12)
      $display("FAIL");
    asc = 8'hAB;
    i = 1;
    if (asc[i -: 2] !== 8'hAB)
      $display("FAIL");
    asc[i -: 2] = 8'h34;
    if (asc !== 8'h34)
      $display("FAIL");
    $display("PASS");
  end
endmodule
