module top;
  typedef struct packed {bit[7:0] hi;bit[7:0] lo;} pair_t;
  typedef union packed {bit[15:0] raw;pair_t pair_value;} packet_t;
  packet_t packet;
  bit[3:0] values[2:3];
  logic selector;
  logic[3:0] uncertain;
  int index;
  initial begin
    packet.raw=16'h3412; index=0;
    packet.pair_value.hi[index+:4]+=4'h2;
    packet.pair_value.lo[index+4+:4]^=4'hf;
    uncertain=4'b1x0z; packet.pair_value.hi[index+:4]^=uncertain;
    values='{4'ha,4'hb}; selector=0; values[selector]+=1;
    $display("two-state %h %h %h",packet.raw,values[2],values[3]);
    $finish;
  end
endmodule
