module top;
  initial begin
    automatic logic signed [7:0] cells[2:0]='{-8'sd2,8'sd3,8'sd4};
    int total;
    total=cells.sum();
    #2;
    cells[1]=-8'sd8;
    $display("automatic %0d %0d",total,cells.sum());
    $finish;
  end
endmodule
