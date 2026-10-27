module top;
  bit [3:0] values [0:1][0:2] = '{'{1, 2, 3}, '{4, 5, 6}};
  int sum;
  // expected self-check line: sum=21
  initial begin
    foreach (values[i,j]) sum += values[i][j];
    $display("sum=%0d", sum);
  end
endmodule
