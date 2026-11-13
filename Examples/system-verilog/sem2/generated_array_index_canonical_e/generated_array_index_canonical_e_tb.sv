module generated_array_index_canonical_e_tb;
 logic [7:0] x; wire [7:0] y;
 generated_array_index_canonical_e dut(.x(x), .y(y));
 initial begin
   #1 $display("ROW i=0 y=%b",y);
   x=8'h00; #1 $display("ROW i=1 y=%b",y);
   x=8'ha5; #1 $display("ROW i=2 y=%b",y);
   x=8'bxxxxxxxx; #1 $display("ROW i=3 y=%b",y);
   x=8'bzzzzzzzz; #1 $display("ROW i=4 y=%b",y);
   x=8'h3c; #1 $display("ROW i=5 y=%b",y);
   x=8'hff; #1 $display("ROW i=6 y=%b",y);
   x=8'h00; #1 $display("ROW i=7 y=%b",y);
   x=8'h01; #1 $display("ROW i=8 y=%b",y);
   $finish;
 end
endmodule
