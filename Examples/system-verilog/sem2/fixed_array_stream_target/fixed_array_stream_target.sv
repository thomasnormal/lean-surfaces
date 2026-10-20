// Right streaming can target a constant fixed-array cell and a scalar leaf.
module fixed_array_stream_target (
    input  logic [4:0] source,
    output logic [3:0] hi,
    output logic       out
);
  logic [3:0] arr [0:1];

  always_comb begin
    {>> {arr[0], out}} = source;
  end
  assign hi = arr[0];
endmodule
