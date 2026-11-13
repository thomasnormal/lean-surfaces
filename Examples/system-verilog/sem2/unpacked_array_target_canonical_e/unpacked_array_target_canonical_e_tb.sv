module unpacked_array_target_canonical_e_tb;
 logic [7:0] x=0; logic idx=0; wire [7:0] y;
 unpacked_array_target_canonical_e dut(.x(x), .idx(idx), .y(y));
 initial begin #1 $display("ROW i=0 y=%b",y); x=8'ha5; #1 $display("ROW i=1 y=%b",y); $finish; end
endmodule
