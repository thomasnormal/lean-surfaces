/*
:name: unpacked_assign
:description: §10.4 — exact positional assignment pattern writes fixed-unpacked cells
:tags: 10.4
:type: simulation
*/
module top;
  logic [7:0] value [0:1];
  initial begin
    value = '{8'h12, 8'h34};
    if (value[0] === 8'h12 && value[1] === 8'h34) $display("PASS");
    else $display("FAIL %h %h", value[0], value[1]);
    $finish;
  end
endmodule
