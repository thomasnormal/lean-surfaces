module memory_implicit_event_canonical_e_tb;
  logic [3:0] d=0; logic [1:0] idx=0; wire [3:0] q;
  memory_implicit_event_canonical_e #(.W(4),.P(2)) dut(.d(d),.idx(idx),.q(q));
  initial begin #1; $display("ROW i=0 q=%b",q); d=4'h3; #1; $display("ROW i=1 q=%b",q); idx=1; #1; $display("ROW i=2 q=%b",q); $finish; end
endmodule
