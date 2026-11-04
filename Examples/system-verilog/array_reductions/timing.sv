module top;
  logic [7:0] a[2:0] = '{8'd2,8'd3,8'd4};
  logic [7:0] copy[-1:1];
  logic [7:0] saved;
  initial begin
    copy=a;
    saved<=a.sum();
    a[1]=8'd20;
    #2;
    $display("snapshot %0d %0d %0d",saved,a.sum(),copy.sum());
    a[2]=8'd10;
    #3;
    $display("live %0d %0d",a.sum(v) with (int'(v)),copy.product());
    $finish;
  end
endmodule
