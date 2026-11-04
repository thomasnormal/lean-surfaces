/*
:name: unpacked_patterns
:description: §10.4 — structured and replicated fixed-unpacked patterns fill cells
:tags: 10.4
:type: simulation
*/
module top;
  logic [7:0] value [0:2];
  initial begin
    value = '{default: 8'h12};
    value = '{3{8'h34}};
    if (value[0] === 8'h34 && value[1] === 8'h34 &&
        value[2] === 8'h34)
      $display("PASS");
    else
      $display("FAIL %h %h %h", value[0], value[1], value[2]);
    $finish;
  end
endmodule
