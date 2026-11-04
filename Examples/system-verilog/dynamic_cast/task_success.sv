module top;
 typedef enum logic [2:0] {A=1, B=6} e_t;
 e_t e; int source; bit [3:0] bits;
 initial begin
  e=A; source=6; $cast(e,source); $cast(bits,8'haf);
  $display("task %b %h",e,bits); $finish;
 end
endmodule
