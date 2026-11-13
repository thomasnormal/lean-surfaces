module function_source_edge_canonical_e_tb;
 logic clk=0, d=0; wire q;
 function_source_edge_canonical_e dut(.clk(clk), .d(d), .q(q));
 initial begin #1 $display("ROW i=0 q=%b",q); clk=1; #1 $display("ROW i=1 q=%b",q); $finish; end
endmodule
