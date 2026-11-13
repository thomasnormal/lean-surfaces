module packed_shift_canonical_e_tb;
  logic clk=0,v=0; wire [3:0] q4; wire [7:0] q8;
  packed_shift_canonical_e #(.N(4)) d4(.clk(clk),.v(v),.q(q4)); packed_shift_canonical_e #(.N(8)) d8(.clk(clk),.v(v),.q(q8));
  initial begin #1; $display("ROW N=4 i=0 q=%b",q4); $display("ROW N=8 i=0 q=%b",q8); v=1; clk=1; #1; $display("ROW N=4 i=1 q=%b",q4); $display("ROW N=8 i=1 q=%b",q8); v=0; clk=0; #1; $display("ROW N=4 i=2 q=%b",q4); $display("ROW N=8 i=2 q=%b",q8); v=1; clk=1; #1; $display("ROW N=4 i=3 q=%b",q4); $display("ROW N=8 i=3 q=%b",q8); $finish; end
endmodule
