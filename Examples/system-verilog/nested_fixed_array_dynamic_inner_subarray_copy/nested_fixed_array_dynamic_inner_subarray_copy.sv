/* A dynamic inner prefix copies a flat row into a bounded three-dimensional array. */
module top;
  logic [3:0] cube [0:1][0:1][0:2];
  logic [3:0] row [5:3];
  logic index;

  initial begin
    cube = '{'{ '{4'h0, 4'h1, 4'h2}, '{4'h3, 4'h4, 4'h5} },
             '{ '{4'h6, 4'h7, 4'h8}, '{4'h9, 4'ha, 4'hb} } };
    row = '{4'hc, 4'hd, 4'he};
    index = 1'b1;
    cube[0][index] = row;
    if (cube[0][1][0] === 4'hc && cube[0][1][1] === 4'hd &&
        cube[0][1][2] === 4'he && cube[0][0][0] === 4'h0 &&
        cube[0][0][1] === 4'h1 && cube[0][0][2] === 4'h2)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
