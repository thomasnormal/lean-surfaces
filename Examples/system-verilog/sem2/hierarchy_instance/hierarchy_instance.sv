module leaf(input wire a, output wire y);
  assign y = a;
endmodule
module hierarchy_instance(input wire a, output wire y);
  leaf u_leaf(.a(a), .y(y));
endmodule
