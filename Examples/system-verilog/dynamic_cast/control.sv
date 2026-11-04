module top;
 typedef enum logic [1:0] {A=1, B=2} e_t;
 e_t e; int r;
 initial begin
  e=A; r=0 && $cast(e,2); $display("and-skip %0d %b",r,e);
  r=1 || $cast(e,2); $display("or-skip %0d %b",r,e);
  r=1 && $cast(e,2); $display("and-write %0d %b",r,e);
  if ($cast(e,3) || $cast(e,1)) $display("fallback %b",e);
  r=1'bx && $cast(e,3); $display("unknown-fail %0d %b",r,e);
  r=($cast(e,2) == 1); $display("comparison %0d %b",r,e);
  $finish;
 end
endmodule
