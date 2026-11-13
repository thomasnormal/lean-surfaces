module net_z_scalar_canonical_e_tb;
 logic clk=0; wire [31:0] q; wire z_out; wire z_bit;
 net_z_scalar_canonical_e dut(.*);
 initial begin #1 $display("ROW i=0 q=%b z_out=%b z_bit=%b",q,z_out,z_bit); clk=1; #1 $display("ROW i=1 q=%b z_out=%b z_bit=%b",q,z_out,z_bit); $finish; end
endmodule
