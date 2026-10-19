/*
:name: unpacked_init
:description: §7.4 — positional fixed-unpacked initializer populates cells
:tags: 7.4
:type: simulation
*/
module top;
  logic [7:0] value [0:1] = '{8'h12, 8'h34};
  initial begin
    if (value[1] === 8'h34) $display("PASS");
    else $display("FAIL %h", value[1]);
    $finish;
  end
endmodule
