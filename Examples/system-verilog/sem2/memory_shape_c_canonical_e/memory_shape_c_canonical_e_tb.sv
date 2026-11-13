module memory_shape_c_canonical_e_tb;
 logic clk=0; logic [3:0] a [0:1]; wire [3:0] q;
 memory_shape_c_canonical_e dut(.*);
 initial begin a[0]=1; a[1]=2; #1 $display("ROW i=0 q=%b",q); clk=1; #1 $display("ROW i=1 q=%b",q); a[0]=3; a[1]=4; clk=0; #1 $display("ROW i=2 q=%b",q); clk=1; #1 $display("ROW i=3 q=%b",q); $finish; end
endmodule
