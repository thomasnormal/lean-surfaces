// The halves of `hier_param.sv`, byte for byte, below a header with one non-ASCII character: this em dash — U+2014.
// The extractor reads the parent's `wire` output as a net-as-variable only where the driver text it slices from the
// source matches; it slices DECODED text with slang's BYTE offsets, so a multi-byte character above the driver shifts the
// slice and `y` stays a loud `PortSymbol:net-z` member (ls-sv's defect, lower_proc.py `net_driver_reason`).
module leaf #(parameter integer W = 4) (input wire [W-1:0] a, output wire [W-1:0] y);
  assign y = a;
endmodule
module hierarchy_parameterized #(parameter integer W = 8) (input wire [W-1:0] a, output wire [W-1:0] y);
  leaf #(.W(W/2)) lo(.a(a[W/2-1:0]), .y(y[W/2-1:0]));
  leaf #(.W(W/2)) hi(.a(a[W-1:W/2]), .y(y[W-1:W/2]));
endmodule
