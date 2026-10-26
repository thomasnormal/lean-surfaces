/*
:name: packed_array_dynamic_index
:description: §7.4.6 — dynamic indexing of a wide nested packed element
:tags: 7.4.6
:type: simulation
*/
module top;
  logic [1:0][3:0] a;
  int i;

  initial begin
    a = 8'hAB;
    i = 1;
    if (a[i] === 4'hA)
      a[i] = 4'hC;
    if (a[1] === 4'hC && a[i] === 4'hC)
      $display("PASS");
    else
      $display("FAIL");
  end
endmodule
