// Round 4 folds, confirming the round 3 repair (verifier repros vp_case,
// vp_case2) with other operators: a negative int parameter inside the items
// of a case wider than 32 bits (N >= 31) is converted to the unsigned
// context before the operator — zero-extended (IEEE 1800-2023 11.8.2, 12.5),
// so `-P`, `P + 2` and `~P` match 2^42 - 2^32 + 3, 2^32 - 1 and
// 2^42 - 2^32 + 2 at N = 40. Icarus 12.0 agrees; Yosys 0.53 evaluates `-P`
// and `~P` at their own 32 bits (synthesis-side divergence 3,
// docs/sv-oracle-disagreements.md).
module fold_rcase #(parameter int N = 7, parameter int P = -3) (
  input  logic [N+1:0] a,
  output logic [1:0]   o1);
  always_comb begin
    case (a)
      -P: o1 = 2'd1;
      P + 2: o1 = 2'd2;
      ~P: o1 = 2'd3;
      default: o1 = 2'd0;
    endcase
  end
endmodule
