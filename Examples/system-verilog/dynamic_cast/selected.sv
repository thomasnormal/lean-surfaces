module top;
 typedef enum logic [3:0] {A=1, B=8} e_t;
 typedef struct packed {logic [3:0] hi;logic [3:0] lo;} pair_t;
 e_t cells[0:1]; pair_t pair; logic [15:0] bits; int i; int r;
 initial begin
  cells[0]=A; cells[1]=A; pair=8'h32; bits=16'habcd; i=1;
  r=$cast(cells[i],8); $display("cell %0d %h %h",r,cells[0],cells[1]);
  r=$cast(cells[i],7); $display("retain %0d %h %h",r,cells[0],cells[1]);
  i=6; r=$cast(cells[i],1); $display("outside %0d %h %h",r,cells[0],cells[1]); i=1;
  r=$cast(bits[4*i+:4],6); $display("window %0d %h",r,bits);
  r=$cast(pair.lo,4'hf); $display("member %0d %h",r,pair);
  $finish;
 end
endmodule
