module function_source_edge_canonical_e_tb;
 logic clk=0, d=0; wire q;
 function_source_edge_canonical_e dut(.clk(clk), .d(d), .q(q));
 initial begin
   #1 $display("ROW i=0 q=%b",q);
   clk=1; #1 $display("ROW i=1 q=%b",q);
   clk=0; d=1'bx; #1 $display("ROW i=2 q=%b",q);
   clk=1; #1 $display("ROW i=3 q=%b",q);
   clk=0; d=1'bz; #1 $display("ROW i=4 q=%b",q);
   clk=1; #1 $display("ROW i=5 q=%b",q);
   clk=0; d=1'b1; #1 $display("ROW i=6 q=%b",q);
   clk=1; #1 $display("ROW i=7 q=%b",q);
   $finish;
 end
endmodule
