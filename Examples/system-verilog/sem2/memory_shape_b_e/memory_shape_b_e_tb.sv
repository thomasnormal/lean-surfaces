module memory_shape_b_e_tb;
  logic clk=0; logic [3:0] d=0; wire [3:0] q; memory_shape_b_e #(.W(4),.P(3)) dut(.clk(clk),.d(d),.q(q));
  initial begin #1; $display("ROW i=0 q=%b",q); d=1; clk=1; #1; $display("ROW i=1 q=%b",q); d=2; clk=0; #1; $display("ROW i=2 q=%b",q); clk=1; #1; $display("ROW i=3 q=%b",q); d=4; clk=0; #1; $display("ROW i=4 q=%b",q); clk=1; #1; $display("ROW i=5 q=%b",q); $finish; end
endmodule
