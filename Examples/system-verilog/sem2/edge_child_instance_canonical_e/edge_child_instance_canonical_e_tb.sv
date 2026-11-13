module edge_child_instance_canonical_e_tb;
 logic clk=0, d=0; wire y;
 edge_parent_canonical_e dut(.clk(clk), .d(d), .y(y));
 initial begin #1 $display("ROW i=0 y=%b",y); clk=1; #1 $display("ROW i=1 y=%b",y); $finish; end
endmodule
