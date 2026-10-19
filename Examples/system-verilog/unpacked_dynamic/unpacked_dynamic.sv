/*
:name: unpacked_dynamic
:description: §7.4.5 — dynamic fixed-unpacked element reads and writes use bounded cells
:tags: 7.4.5
:type: simulation
*/
module top;
  logic [7:0] value [0:1];
  logic [1:0] index;
  initial begin
    index = 1;
    value[index] = 8'h34;
    if (value[index] === 8'h34) $display("PASS1");
    else $display("FAIL1 %h", value[index]);
    index = 2;
    value[index] = 8'h55;
    if (value[index] === 8'hxx) $display("PASS2");
    else $display("FAIL2 %h", value[index]);
    index = 2'bx;
    value[index] = 8'h77;
    if (value[index] === 8'hxx) $display("PASS3");
    else $display("FAIL3 %h", value[index]);
    $finish;
  end
endmodule
