// `$bits` of a declared signal (an elaboration-time constant: its type is
// read, never its value) in indexed part-select labels, reads and a target.
module bits_labels #(parameter int N = 6) (
  input  logic [N-1:0] a,
  input  logic [7:0]   v,
  output logic [1:0]   o1,
  output logic [1:0]   o2,
  output logic [1:0]   o3,
  output logic [7:0]   y
);
  assign o1 = v[$bits(a) - 1 -: 2];
  assign o2 = v[$bits(a) +: 2];
  assign o3 = v[$clog2($bits(a)) +: 2];
  always_comb begin
    y = '0;
    y[$bits(a) - 3 +: 2] = 2'b11;
  end
endmodule
