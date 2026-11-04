/* A dynamic outer index copies a flat row into a bounded multidimensional array. */
module top;
  logic [3:0] matrix [3:2][0:2];
  logic [3:0] row [7:5];
  logic [1:0] outer_index;

  initial begin
    matrix = '{'{4'hc, 4'hd, 4'he}, '{4'hf, 4'ha, 4'hb}};
    row = '{4'h1, 4'h2, 4'h3};
    outer_index = 2'd2;
    matrix[outer_index] = row;
    if (matrix[2][0] === 4'h1 && matrix[2][1] === 4'h2 &&
        matrix[2][2] === 4'h3 && matrix[3][0] === 4'hc &&
        matrix[3][1] === 4'hd && matrix[3][2] === 4'he)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
