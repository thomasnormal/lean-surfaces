// Phase-2 probe: select reads, part-select, replication, reductions,
// width conversion — parametric (the family is instantiated at W=8 and
// W=16 by the harness).
module t2_sel #(parameter W = 8) (
    input  logic [W-1:0] a,
    input  logic [$clog2(W)-1:0] i,
    output logic bit_o,
    output logic [3:0] nib_o,
    output logic [2*W-1:0] rep_o,
    output logic ror_o, rand_o, rxor_o, rnor_o,
    output logic [W+3:0] ext_o
);
  assign bit_o  = a[i];
  assign nib_o  = a[4:1];
  assign rep_o  = {2{a}};
  assign ror_o  = |a;
  assign rand_o = &a;
  assign rxor_o = ^a;
  assign rnor_o = ~|a;
  assign ext_o  = a;  // implicit zero-extending width conversion
endmodule
