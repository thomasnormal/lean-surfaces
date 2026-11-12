module mem_order_e_tb;
  logic [7:0] a = 8'h12;
  wire [7:0] y, q;
  mem_order_e dut(.a(a), .y(y), .q(q));
  initial begin
    #1 $display("ROW first y=%h q=%h", y, q);
    a = 8'ha5;
    #1 $display("ROW second y=%h q=%h", y, q);
    $finish;
  end
endmodule
