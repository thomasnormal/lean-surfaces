// Two always_comb blocks writing DIFFERENT bits of one variable `t`; the
// second reads all of `t` (the self-read guard ADMITS each block: neither
// reads a bit it writes later). Legal: IEEE 1800-2023 §9.2.2.2 and §6.5
// allow independent elements of a variable (each bit of a packed type) to
// be assigned by different processes, as ls-sv's bit-granular one-driver
// rule does. §9.2.2.2.1 puts the expansions of the read `t` in the second
// block's implicit sensitivity list except the bit it writes, so t[0] is
// in it: Xcelium 24.03, Verilator 5.042 and run2 re-run the block when t[0]
// changes (y = {b, a}). Icarus 12.0 leaves ALL of `t` out (`iverilog
// -g2012` netlist: the block's event is `anyedge, b` alone), without a
// diagnostic, and shows the previous t[0] until `b` changes: an Icarus
// departure, declared on the harness/sv/cases2.json row
// (`oracle_disagreement` `iverilog-comb-bit-split-sensitivity`) and in
// docs/sv-oracle-disagreements.md, with the wider class it belongs to.
module acg_xproc_bits (
  input  logic       a, b,
  output logic [1:0] y
);
  logic [1:0] t;
  always_comb t[0] = a;
  always_comb begin
    t[1] = b;
    y = t;
  end
endmodule
