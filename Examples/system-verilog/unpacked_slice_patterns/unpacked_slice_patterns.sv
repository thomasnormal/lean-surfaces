/*
:name: unpacked_slice_patterns
:description: §10.4 — structured and replicated patterns fill a fixed-array slice
:tags: 10.4
:type: simulation
*/
module top;
  logic [7:0] value [0:3];
  initial begin
    value[1:2] = '{default: 8'h12};
    value[1:2] = '{2{8'h34}};
    if (value[1] === 8'h34 && value[2] === 8'h34)
      $display("PASS");
    else
      $display("FAIL %h %h", value[1], value[2]);
    $finish;
  end
endmodule
