module top;
  logic [1:0][3:0] value = '{4'ha, 4'h5};
  initial begin $display("multidim %h", value); $finish; end
endmodule
