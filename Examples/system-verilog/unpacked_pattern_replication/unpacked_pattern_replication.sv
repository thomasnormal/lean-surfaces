/*
:name: unpacked_pattern_replication
:description: §5.11 — nested replication of positional array-pattern elements
:tags: 5.11
:type: simulation
*/
module top;
  int value [1:6];
  initial begin
    value = '{3{4, 5}};
    if (value[1] === 4 && value[2] === 5 && value[3] === 4 &&
        value[4] === 5 && value[5] === 4 && value[6] === 5)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
