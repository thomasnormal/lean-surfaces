/*
:name: unpacked_slice_copy
:description: §10.4 — constant fixed-unpacked slices copy cellwise
:tags: 10.4
:type: simulation
*/
module top;
  logic [7:0] source [0:3];
  logic [7:0] value [0:3];
  initial begin
    source[2] = 8'h12;
    source[3] = 8'h34;
    value[1:2] = source[2:3];
    if (value[1] === 8'h12 && value[2] === 8'h34)
      $display("PASS");
    else
      $display("FAIL %h %h", value[1], value[2]);
    $finish;
  end
endmodule
