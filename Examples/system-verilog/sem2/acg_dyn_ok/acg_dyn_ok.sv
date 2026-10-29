// Run-time indices on a variable written whole first (ADMITTED): the read
// `t[s]` may read any bit of `t`, but every bit is already written; the
// run-time write `t[s] = b` may write any bit later, but no later read sees
// an unwritten bit (`z = t` comes after every write of `t`).
// Admitted by the always_comb self-read guard (LeanModels/Sv/CombGuard2.lean).
module acg_dyn_ok (
  input  logic [3:0] a,
  input  logic [1:0] s,
  input  logic       b,
  output logic       y,
  output logic [3:0] z
);
  logic [3:0] t;
  always_comb begin
    t = a;
    y = t[s];
    t[s] = b;
    z = t;
  end
endmodule
