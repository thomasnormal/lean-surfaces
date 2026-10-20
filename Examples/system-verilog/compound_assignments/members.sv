module top;
  typedef struct packed {logic[7:0] hi;logic[7:0] lo;} pair_t;
  typedef union packed {logic[15:0] raw;pair_t pair_value;} packet_t;
  packet_t packet;
  int index;
  logic[31:0] unknown_index;
  initial begin
    packet.raw=16'h3412; index=0;
    packet.pair_value.hi[index+:4]+=4'h2;
    packet.pair_value.lo[index+4+:4]^=4'hf;
    $display("members %h",packet.raw);
    index=30; packet.pair_value.hi[index-:4]+=4'h1;
    unknown_index='x; packet.pair_value.lo[unknown_index]^=1'b1;
    $display("invalid %h",packet.raw);
    $finish;
  end
endmodule
