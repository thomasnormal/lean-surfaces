module net_generated_driver_canonical_e_tb;
 logic clk=0; wire [31:0] q; wire z_out;
 net_generated_driver_canonical_e dut(.*);
 initial begin #1 $display("ROW i=0 q=%b z_out=%b",q,z_out); clk=1; #1 $display("ROW i=1 q=%b z_out=%b",q,z_out); $finish; end
endmodule
