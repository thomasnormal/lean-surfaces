// SIZED SIGNED literals assigned to parameter-width targets: slang's fold
// sign-extended them to the DEFAULT context width, which the model then
// zero-extended at every wider point. They are a `SignedResize` of the
// literal at its own width, sign-extended (or truncated) at the
// instantiated width (IEEE 1800-2023 §11.8.2, §10.7).
module int_const_sized #(parameter int N = 7) (
  input  logic [3:0]   a,
  output logic [N+1:0] o1,
  output logic [N+1:0] o2,
  output logic [N+1:0] o3
);
  assign o1 = 4'sb1000;
  assign o2 = 4'sd3;
  assign o3 = 12'shF80;
endmodule
