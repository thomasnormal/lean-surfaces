module generate_hierarchy_memory_canonical_e_tb;
 logic clk=0; logic [3:0] d=0; wire [3:0] q0;
 generate_hierarchy_memory_canonical_e dut(.*);
 initial begin #1 $display("ROW i=0 q=%b",q0);  $finish; end
endmodule
