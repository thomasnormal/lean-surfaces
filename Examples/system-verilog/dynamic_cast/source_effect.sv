module top;
 typedef enum logic [2:0] {A=1, B=6} e_t;
 e_t e; int r; int source;
 initial begin e=B; source=0; r=$cast(e,++source); $display("effect %0d %b %0d",r,e,source); $finish; end
endmodule
