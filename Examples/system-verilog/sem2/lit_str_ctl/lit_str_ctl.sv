// WP-R-D: the named control escapes of IEEE 1800-2023 Table 5-1 in string literals: \a (bell, 7), \v (vertical tab, 11) and \f (form feed, 12). slang, Icarus 12, Verilator 5.042 and Yosys 0.53 produce the table's bytes; Xcelium 24.03 reads each as the plain letter (a = 0x61, v = 0x76, f = 0x66), a DECLARED departure (Thomas 2026-11-01: an Xcelium-only dissent is not a tools split). `ya yv yf` are the literals alone, `yall` the three in one literal, `yloc` a localparam built from one, `yx` and `eq` use one as a run-time operand (a = 8'h76 is the plain letter v: `eq` is 0 in the model and 1 in Xcelium).
module lit_str_ctl (
  input  logic [7:0]  a,
  output logic [7:0]  ya,
  output logic [7:0]  yv,
  output logic [7:0]  yf,
  output logic [23:0] yall,
  output logic [7:0]  yloc,
  output logic [7:0]  yx,
  output logic        eq
);
  localparam logic [7:0] P = "\a";
  assign ya   = "\a";
  assign yv   = "\v";
  assign yf   = "\f";
  assign yall = "\a\v\f";
  assign yloc = P + 8'd1;
  assign yx   = a ^ "\f";
  assign eq   = (a == "\v");
endmodule
