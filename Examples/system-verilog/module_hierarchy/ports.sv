module leaf(input logic source,output logic value);
  assign value=source;
endmodule
module top;
  logic source=1,value;
  leaf child(source,value);
  initial begin #1;$display("ports %b",value);$finish;end
endmodule
