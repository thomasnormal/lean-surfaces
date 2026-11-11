module pow_wall_tb;
  logic [7:0] y;
  pow_wall #(.W(8193)) d(.y(y));
  initial begin
    #1 $display("ROW large y=%h", y);
    $finish;
  end
endmodule
