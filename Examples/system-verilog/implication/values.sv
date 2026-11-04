module top;
  logic a, b;
  logic [1:0] u; logic [2:0] v;
  logic [64:0] wide;
  initial begin
    a = 1'b0; b = 1'b0; $display("00 %b", a -> b);
    a = 1'b0; b = 1'b1; $display("01 %b", a -> b);
    a = 1'b0; b = 1'bx; $display("0x %b", a -> b);
    a = 1'b0; b = 1'bz; $display("0z %b", a -> b);
    a = 1'b1; b = 1'b0; $display("10 %b", a -> b);
    a = 1'b1; b = 1'b1; $display("11 %b", a -> b);
    a = 1'b1; b = 1'bx; $display("1x %b", a -> b);
    a = 1'b1; b = 1'bz; $display("1z %b", a -> b);
    a = 1'bx; b = 1'b0; $display("x0 %b", a -> b);
    a = 1'bx; b = 1'b1; $display("x1 %b", a -> b);
    a = 1'bx; b = 1'bx; $display("xx %b", a -> b);
    a = 1'bx; b = 1'bz; $display("xz %b", a -> b);
    a = 1'bz; b = 1'b0; $display("z0 %b", a -> b);
    a = 1'bz; b = 1'b1; $display("z1 %b", a -> b);
    a = 1'bz; b = 1'bx; $display("zx %b", a -> b);
    a = 1'bz; b = 1'bz; $display("zz %b", a -> b);
    u = 2'b1x; v = 3'b0xz;
    $display("vectors %b", u -> v);
    u = 2'b00; v = 3'bxxx;
    $display("zero %b", u -> v);
    wide = u -> v;
    $display("wide %h", wide);
    $display("context %b %b", (1'b0 -> 1'bx) + 8'b0, (1'b1 -> 1'bx) + 8'b0);
    $display("nested %b %b", 1'b0 -> 1'b1 -> 1'b0, (1'b0 -> 1'b1) -> 1'b0);
    $finish;
  end
endmodule

// Independent observation: 2026-10-20, group pure-implication.
// Source SHA256 before this trailing observation block:
// cddd8a96fecea0354b39a62cbaf48f1382cadbb0ba39270327938c5ca88aedf7
// Mapping: labeled displays are compared verbatim, without projection.
