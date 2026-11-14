module unpacked_array_target_canonical_e_tb;
 logic [7:0] x; logic idx; wire [7:0] y;
 unpacked_array_target_canonical_e dut(.x(x), .idx(idx), .y(y));
 initial begin
   #1 $display("ROW i=0 y=%b",y);
   x=8'h00; idx=1'b0; #1 $display("ROW i=1 y=%b",y);
   x=8'ha5; idx=1'b1; #1 $display("ROW i=2 y=%b",y);
   x=8'h3c; idx=1'b0; #1 $display("ROW i=3 y=%b",y);
   x=8'bxxxxxxxx; idx=1'b1; #1 $display("ROW i=4 y=%b",y);
   x=8'h5a; idx=1'bx; #1 $display("ROW i=5 y=%b",y);
   x=8'bzzzzzzzz; idx=1'b0; #1 $display("ROW i=6 y=%b",y);
   x=8'h96; idx=1'bz; #1 $display("ROW i=7 y=%b",y);
   x=8'h0f; idx=1'b1; #1 $display("ROW i=8 y=%b",y);
   $finish;
 end
endmodule
