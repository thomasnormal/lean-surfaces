/*
:name: packed_array_dynamic_target
:description: §7.4.6 — dynamic target on an ascending packed vector
:tags: 7.4.6
:type: simulation
*/
module top;
  logic [0:7] a;
  int i;

  initial begin
    a = 8'b0;
    i = 2;
    a[i] = 1'b1;
    if (a[2] === 1'b1 && a[i] === 1'b1)
      $display("PASS");
    else
      $display("FAIL");
  end
endmodule
