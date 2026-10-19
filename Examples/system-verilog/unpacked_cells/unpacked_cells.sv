/*
:name: unpacked_cells
:description: §10.2 — constant fixed-unpacked array elements lower to cells
:tags: 10.2
:type: simulation
*/
module top;
  logic [7:0] mem [0:3];
  initial begin
    mem[2] = 8'hAB;
    if (mem[2] === 8'hAB) $display("PASS");
    else $display("FAIL %h", mem[2]);
    $finish;
  end
endmodule
