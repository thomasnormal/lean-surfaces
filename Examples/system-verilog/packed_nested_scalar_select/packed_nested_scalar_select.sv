/*
:name: packed_nested_scalar_select
:description: §7.4.1 — constant scalar selections through nested packed arrays
:tags: 7.4.1
:type: simulation
*/
module top;
  logic [1:0][3:0] down;
  logic [0:1][0:3] up;

  initial begin
    down = '0;
    up = '0;
    down[1][2] = 1'b1;
    down[0][3:2] = 2'b10;
    down[1][0] = 1'bx;
    up[0][0] = 1'b1;
    up[1][3] = 1'b1;
    if (down[1][2] === 1'b1 &&
        down[0][3:2] === 2'b10 &&
        down[1][0] === 1'bx &&
        up[0][0] === 1'b1 && up[1][3] === 1'b1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
