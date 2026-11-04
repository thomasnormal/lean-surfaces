// A direct continuous concatenation uses the semantic tier's existing
// per-slice driver windows and samples the RHS once per comb pass.
module concat_assign (
    input  logic [7:0] source,
    output logic [3:0] upper,
    output logic [3:0] lower
);
  assign {upper, lower} = source;
endmodule
