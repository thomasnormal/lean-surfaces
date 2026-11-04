module top;
 typedef enum logic [1:0] {A=1, B=2, X=2'bx1, Z=2'bz0} e_t;
 typedef enum bit [1:0] {C=0, D=1} b_t;
 typedef enum logic signed [2:0] {N=-2, P=2} s_t;
 e_t e; b_t b; s_t s; int r; int v;
 initial begin
  e=B; r=$cast(e,5); $display("wide %0d %b",r,e);
  r=$cast(e,32'hffff_ffff); $display("ones %0d %b",r,e);
  r=$cast(e,2'bx1); $display("x %0d %b",r,e);
  r=$cast(e,2'bz0); $display("z %0d %b",r,e);
  b=D; r=$cast(b,2'bxx); $display("two %0d %b",r,b);
  r=$cast(b,2'bx1); $display("two1 %0d %b",r,b);
  s=P; r=$cast(s,-2); $display("sign %0d %b",r,s);
  r=$cast(s,3'b110); $display("unsigned %0d %b",r,s);
  r=$cast(s,32'd6); $display("u32 %0d %b",r,s);
  r=$cast(s,32'hffff_fffe); $display("u32n %0d %b",r,s);
  e=e_t'(3); r=$cast(e,e); $display("selfinvalid %0d %b",r,e);
  v=7; r=$cast(v,2'bxz); $display("int %0d %h",r,v);
  $finish;
 end
endmodule
