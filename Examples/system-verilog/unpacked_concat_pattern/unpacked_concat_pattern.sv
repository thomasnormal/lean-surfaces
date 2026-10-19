/*
:name: unpacked_concat_pattern
:description: §10.10.1 — typed assignment-pattern operand in unpacked concat
:tags: 10.10.1
:type: simulation
*/
module top;
  typedef int AI3 [1:3];
  AI3 source;
  int value [1:9];
  initial begin
    source = '{1, 2, 3};
    value = {source, 4, AI3'{5, 6, 7}, 8, 9};
    if (value[1] === 1 && value[5] === 5 && value[9] === 9)
      $display("PASS");
    else
      $display("FAIL %0d %0d %0d", value[1], value[5], value[9]);
    $finish;
  end
endmodule
