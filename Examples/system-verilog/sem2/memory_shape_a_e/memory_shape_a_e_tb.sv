`timescale 1ns/1ps
module memory_shape_a_e_tb;
  logic clk=0; logic [7:0] d=0; logic [2:0] idx=0; wire [3:0] q0,sel0; wire [7:0] q1,sel1;
  memory_shape_a_e #(.W(4),.P(3)) d0(.clk(clk),.d(d[3:0]),.idx(idx),.q(q0),.selected(sel0));
  memory_shape_a_e #(.W(8),.P(5)) d1(.clk(clk),.d(d),.idx(idx),.q(q1),.selected(sel1));
  initial begin
    #1; $display("ROW W=4,P=3 i=0 q=%b selected=%b",q0,sel0); $display("ROW W=8,P=5 i=0 q=%b selected=%b",q1,sel1);
    d=8'd1; idx=0; clk=1; #1; $display("ROW W=4,P=3 i=1 q=%b selected=%b",q0,sel0); $display("ROW W=8,P=5 i=1 q=%b selected=%b",q1,sel1);
    d=8'd2; idx=1; clk=0; #1; $display("ROW W=4,P=3 i=2 q=%b selected=%b",q0,sel0); $display("ROW W=8,P=5 i=2 q=%b selected=%b",q1,sel1);
    clk=1; #1; $display("ROW W=4,P=3 i=3 q=%b selected=%b",q0,sel0); $display("ROW W=8,P=5 i=3 q=%b selected=%b",q1,sel1);
    d=8'd4; idx=2; clk=0; #1; $display("ROW W=4,P=3 i=4 q=%b selected=%b",q0,sel0); $display("ROW W=8,P=5 i=4 q=%b selected=%b",q1,sel1);
    clk=1; #1; $display("ROW W=4,P=3 i=5 q=%b selected=%b",q0,sel0); $display("ROW W=8,P=5 i=5 q=%b selected=%b",q1,sel1);
    d=8'd8; idx=3'bxxx; clk=0; #1; $display("ROW W=4,P=3 i=6 q=%b selected=%b",q0,sel0); $display("ROW W=8,P=5 i=6 q=%b selected=%b",q1,sel1); $finish;
  end
endmodule
