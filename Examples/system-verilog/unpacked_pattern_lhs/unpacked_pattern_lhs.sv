/*
:name: unpacked_pattern_lhs
:description: §10.9.11 — positional unpacked assignment-pattern LHS
:tags: 10.9.11
:type: simulation
*/
typedef int U3 [0:2];
module top;
  int source [0:2];
  byte a, b, c;
  initial begin
    source = '{11, 22, 33};
    U3'{a, b, c} = source;
    if (a === 11 && b === 22 && c === 33)
      $display("PASS");
    else
      $display("FAIL %0d %0d %0d", a, b, c);
    $finish;
  end
endmodule
