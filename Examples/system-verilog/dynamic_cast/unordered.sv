module top;
 typedef enum logic [2:0] {A=1, B=6} e_t;
 e_t e; int r;
 initial begin e=A; r=$cast(e,6)+int'(e); $display("unordered %0d %b",r,e); $finish; end
endmodule
