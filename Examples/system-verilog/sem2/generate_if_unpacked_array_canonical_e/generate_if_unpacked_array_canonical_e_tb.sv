module generate_if_unpacked_array_canonical_e_tb;
 logic [7:0] x=0; wire [7:0] y;
 generate_if_unpacked_array_canonical_e dut(.x(x), .y(y));
 initial begin #1 $display("ROW i=0 y=%b",y); x=8'ha5; #1 $display("ROW i=1 y=%b",y); $finish; end
endmodule
