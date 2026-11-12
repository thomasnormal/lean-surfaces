// A select of a signed signal inside the instantiated child: the child's own processes are read as a flat design
// without signed reads, so the child is refused.
module signed_child_leaf (
    input logic signed [7:0] a,
    output logic y
);
    assign y = a[7];
endmodule

module signed_child (
    input logic signed [7:0] x,
    output logic y
);
    signed_child_leaf leaf(.a(x), .y(y));
endmodule
