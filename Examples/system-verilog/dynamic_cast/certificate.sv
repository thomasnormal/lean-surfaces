module top;
 typedef enum logic [3:0] {A=1, B=8} e_t;
 e_t destination; logic [3:0] source; int status;
 initial begin
  source=8;
  status=$cast(destination,source);
  $display("certificate %0d %h",status,destination);
  $finish;
 end
endmodule
