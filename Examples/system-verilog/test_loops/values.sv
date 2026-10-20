module top;
 integer n, sum, tails;
 logic [3:0] guard;
 logic [7:0] proof_value;
 initial begin
 n=0; while(0) n++; $display("while_false %0d",n);
 n=0; do n++; while(0); $display("do_false %0d",n);
 guard=4'bx0z0; n=0; while(guard) n++; $display("while_unknown %0d",n);
 n=0; do n++; while(guard); $display("do_unknown %0d",n);
 guard=4'b1xz0; n=0; while(guard) begin n++; guard=4'b0xz0; end
 $display("while_known_one %0d",n);
 n=0;sum=0; do begin n++;if(n==3)continue;sum+=n;end while(n<5);
 $display("do_continue %0d %0d",n,sum);
 n=0;sum=0; while(n<5) begin n++;if(n==3)continue;sum+=n;end
 $display("while_continue %0d %0d",n,sum);
 n=0;do begin n++;break;n++;end while(1); $display("do_break %0d",n);
 n=0;while(1) begin n++;break;n++;end $display("while_break %0d",n);
 tails=0;n=0;do begin n++;while(1)begin tails++;break;end end while(n<2);
 $display("nested %0d %0d",n,tails);
 proof_value=8'ha5;
 while(0) proof_value=8'h5a;
 $display("pretest %h",proof_value);
 do proof_value=8'h5a; while(0);
 $display("posttest %h",proof_value);
 do break; while(guard);
 $finish;
 end
endmodule
