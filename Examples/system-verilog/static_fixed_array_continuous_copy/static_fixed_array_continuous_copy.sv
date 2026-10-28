/*
:name: static_fixed_array_continuous_copy
:description: §7.6 — a fixed unpacked array with an immutable literal initializer can drive a wire array cellwise
:tags: 7.6 continuous assignment
:type: simulation
*/
module top;
  logic [7:0] source [0:1] = '{8'h12, 8'h34};
  wire  [7:0] driven [1:0];
  logic [7:0] value [1:0];

  assign driven = source;

  initial begin
    value = driven;
    if (value[1] === 8'h12 && value[0] === 8'h34)
      $display("PASS");
    else
      $display("FAIL %h %h", value[1], value[0]);
    $finish;
  end
endmodule
