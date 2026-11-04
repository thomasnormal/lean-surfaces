/*
:name: unpacked_concat
:description: §10.10 — unpacked-array concatenation fills fixed-array cells
:tags: 10.10
:type: simulation
*/
module top;
  int value [1:3];
  initial begin
    value = {1, 2, 3};
    if (value[1] === 1 && value[2] === 2 && value[3] === 3)
      $display("PASS");
    else
      $display("FAIL %0d %0d %0d", value[1], value[2], value[3]);
    $finish;
  end
endmodule
