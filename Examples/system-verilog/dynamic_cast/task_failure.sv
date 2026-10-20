module top;
 typedef enum logic [2:0] {A=1, B=6} e_t;
 e_t e;
 initial begin e=A; $cast(e,3); $display("task-failure %b",e); $finish; end
endmodule
