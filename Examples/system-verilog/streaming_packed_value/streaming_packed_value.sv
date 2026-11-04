// Whole packed values retain field order and four-state data when unpacked.
module top;
  typedef struct packed {
    logic [2:0] header;
    logic [4:0] payload;
  } packet_t;
  typedef union packed {
    logic [3:0] first;
    logic [3:0] second;
  } alias_t;

  initial begin
    packet_t packet;
    alias_t shared;
    logic tail;
    {>> {packet, tail}} = 9'b10110xz01;
    $display("%b %b %b", packet.header, packet.payload, tail);
    if (packet.header !== 3'b101 || packet.payload !== 5'b10xz0 ||
        tail !== 1'b1) begin
      $display("FAIL packet");
      $finish;
    end
    {>> {shared, tail}} = 5'b01101;
    $display("%b %b", shared.first, shared.second);
    if (shared.first !== 4'b0110 || shared.second !== 4'b0110)
      $display("FAIL alias");
    else
      $display("PASS");
    {>> {shared, tail}} = 8'b10xz1011;
    $display("%b %b", shared.second, tail);
    if (shared.first !== 4'b10xz || tail !== 1'b1)
      $display("FAIL leading bits");
    $finish;
  end
endmodule
