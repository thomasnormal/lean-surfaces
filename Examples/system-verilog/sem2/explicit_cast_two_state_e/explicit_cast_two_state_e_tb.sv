module explicit_cast_two_state_e_tb;
  bit [3:0] x; wire [7:0] y8; wire [1:0] y2;
  explicit_cast_two_state_e #(.W(8)) d8(.x(x),.y(y8)); explicit_cast_two_state_e #(.W(2)) d2(.x(x),.y(y2));
  initial begin x=0; #1; $display("ROW W=8 y=%b",y8); $display("ROW W=2 y=%b",y2); x=10; #1; $display("ROW W=8 y=%b",y8); $display("ROW W=2 y=%b",y2); x=15; #1; $display("ROW W=8 y=%b",y8); $display("ROW W=2 y=%b",y2); $finish; end
endmodule
