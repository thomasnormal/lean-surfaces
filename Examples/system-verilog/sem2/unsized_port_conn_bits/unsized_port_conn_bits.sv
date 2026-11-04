// Unsized based 0/1 literals widen to the connected input port's width.
module unsized_port_conn_bits_child (
  input logic [7:0] a,
  output logic [7:0] y
);
  assign y = a;
endmodule

module unsized_port_conn_bits (
  output logic [7:0] y0,
  output logic [7:0] y1
);
  unsized_port_conn_bits_child c0 (.a('b0), .y(y0));
  unsized_port_conn_bits_child c1 (.a('b1), .y(y1));
endmodule
