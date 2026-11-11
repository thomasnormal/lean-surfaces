module generate_wall_tb;
  logic [7:0] a;
  logic [7:0] y;
  generate_wall #(.NS(8)) d(.a(a), .y(y));
  initial begin
    a = 8'h00; #1 $display("ROW zero y=%h", y);
    a = 8'ha5; #1 $display("ROW pattern y=%h", y);
    $finish;
  end
endmodule
