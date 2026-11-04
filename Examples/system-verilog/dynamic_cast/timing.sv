module top;
 typedef enum logic [3:0] {A=1, B=8} e_t;
 e_t e; logic [3:0] source; logic [3:0] saved; int r;
 initial begin
  e=A; source=8;
  #2; r=$cast(e,source); saved<=e; source=7;
  #1; $display("capture %0d %h %h %h",r,e,saved,source);
  r=$cast(e,source);
  #2; $display("failure %0d %h %h",r,e,saved);
  $finish;
 end
endmodule
