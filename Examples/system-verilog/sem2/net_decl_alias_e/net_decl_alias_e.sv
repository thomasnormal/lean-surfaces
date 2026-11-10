// Clean-room source-shaped witness for IEEE 1800-2023 §§6.7 and 10.3.
// A net declaration assignment is a continuous driver, not a one-time
// initializer.  The E route retains the node and refuses its execution until
// declaration activation is available.
module net_decl_alias_e(input wire a, output logic q);
  wire t = a;
  assign q = t;
endmodule
