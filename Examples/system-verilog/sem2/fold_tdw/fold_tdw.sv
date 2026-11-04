// Round 6 folds (round 5 FOLDS verifier blocker 2, repros `vs_td2`,
// `vs_td4`): a localparam whose TYPEDEF'd type has a parameter-dependent
// width. The type syntax carries no dimensions, and the envelope used to
// hold slang's elaborated bounds — the default point's [31:0] — so the model
// read TS and TB at 32 bits at every M (`TS + a` at M = 8: 4294967310 against
// 270 in Icarus 12.0 and the Yosys 0.53 netlist). Refused: the type is loud
// ("unrecoverable packed dimensions"). The fixed-width typedefs run
// (`fold_tdf`).
module fold_tdw #(parameter int M = 32) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2);
  typedef logic signed [M-1:0] st_t;
  typedef bit [M-1:0] bt_t;
  localparam st_t TS = -1;
  localparam bt_t TB = -1;
  assign o1 = TS + a;
  assign o2 = TB + a;
endmodule
