module top;
 typedef enum logic [2:0] {A=1, B=6} e_t;
 e_t e; int r; logic choose;
 initial begin e=A; choose=1; r=choose?$cast(e,6):0; $display("conditional %0d %b",r,e); $finish; end
endmodule
