// WP-G four-state contract (S2): reduction operators on a 4-bit vector. `|v` is 1 when some bit is a definite 1 even with x/z elsewhere, 0 when all bits are 0, else x; `&v` is 0 when some bit is a definite 0, 1 when all bits are 1, else x; `^v` is x as soon as one bit is x/z; the negated forms invert a known result and keep x. Pinned against Xcelium 24.03.
module wpg_red (
  input  logic [3:0] v,
  output logic ro,
  output logic ra,
  output logic rx,
  output logic rno,
  output logic rna,
  output logic rnx
);
  assign ro = |v;
  assign ra = &v;
  assign rx = ^v;
  assign rno = ~|v;
  assign rna = ~&v;
  assign rnx = ~^v;
endmodule
