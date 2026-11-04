module leaf;
  int value=3;
endmodule
module top;
  leaf a[2:-1](),grid[3:0]();
  initial begin
    #1;
    a[2].value=11;
    a[-1].value=22;
    grid[0].value=33;
    $display("array %0d %0d %0d %0d",a[2].value,a[1].value,a[0].value,a[-1].value);
    $display("grid %0d %0d %0d %0d",grid[3].value,grid[2].value,grid[1].value,grid[0].value);
    $finish;
  end
endmodule
