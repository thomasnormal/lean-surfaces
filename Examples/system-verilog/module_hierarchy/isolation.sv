module leaf #(parameter logic[7:0] P=8'h11);
  logic[7:0] value=P;
endmodule
module top;
  leaf left(),right();
  initial begin
    #1;
    $display("before %h %h",left.value,right.value);
    left.value+=8'h10;
    $display("blocking %h %h",left.value,right.value);
    right.value<=left.value;
    left.value=8'h33;
    #1;
    $display("captured %h %h",left.value,right.value);
    $finish;
  end
endmodule
