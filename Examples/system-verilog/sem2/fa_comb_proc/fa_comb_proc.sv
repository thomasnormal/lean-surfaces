// A full adder as ONE always_comb: a temporary, a blocking read of it, and an
// if/else. The hand-built twin `LeanModels.Sv.Comb2ProcExample.faDesign` is
// lowered to one continuous assign by symbolic execution and proved correct
// (`fa_correct`, `fa_terminates`).
module fa_comb_proc (
  input  logic a, b, cin,
  output logic s, cout
);
  logic t;
  always_comb begin
    t = a ^ b;
    s = t ^ cin;
    if (t) cout = cin;
    else cout = a;
  end
endmodule
