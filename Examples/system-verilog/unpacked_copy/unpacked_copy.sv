/*
:name: unpacked_copy
:description: §7.6 — equal-length fixed-unpacked array assignment copies cells in declaration order
:tags: 7.6
:type: simulation
*/
module top;
  logic [7:0] source [0:1];
  logic [7:0] value [0:1];
  initial begin
    source[0] = 8'h12;
    source[1] = 8'h34;
    value = source;
    if (value[0] === 8'h12 && value[1] === 8'h34) $display("PASS");
    else $display("FAIL %h %h", value[0], value[1]);
    $finish;
  end
endmodule
