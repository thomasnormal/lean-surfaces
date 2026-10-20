package ArrayStore;
  int values [0:1] = '{2, 7};
endpackage
module top;
  initial begin $display("array %0d", ArrayStore::values[1]); $finish; end
endmodule
