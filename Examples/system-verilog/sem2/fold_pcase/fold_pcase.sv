// Round 3 repair (verifier repros vp_case, vp_case2, vp_idx): a NEGATIVE
// int parameter as a simple operand in the SYMBOLIC positions of a value
// expression — a case item and a select index. At the default N = 7 the
// case compares, and the index computes, at 32 bits (the int's own width);
// where `a` is wider (N >= 31) IEEE 1800-2023 11.8.2 zero-extends `P` into
// the unsigned context (Icarus 12.0 and Yosys 0.53 agree). The envelope
// keeps slang's conversion as a `Resize` marker there too, which Lean
// zero-extends from P's own 32 bits.
module fold_pcase #(parameter int N = 7, parameter int P = -3) (
  input  logic [N+1:0] a,
  input  logic [7:0]   v,
  output logic [1:0]   o1,
  output logic [1:0]   o2,
  output logic         o3
);
  always_comb begin
    case (a)
      P: o1 = 2'd1;
      default: o1 = 2'd0;
    endcase
  end
  always_comb begin
    case (a + 1'b0)
      P + 1'b0: o2 = 2'd1;
      P - 1: o2 = 2'd2;
      default: o2 = 2'd0;
    endcase
  end
  assign o3 = v[a - P];
endmodule
