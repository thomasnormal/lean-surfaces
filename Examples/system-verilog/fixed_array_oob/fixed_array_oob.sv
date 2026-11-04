/*
:name: fixed_array_oob
:description: an out-of-bounds fixed unpacked array write is a no-op
:tags: 7.4.5
:type: simulation
*/
module top;
  int values [0:3];
  initial begin
    values[0] = 42;
    values[99] = 999;
    if (values[0] == 42)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
