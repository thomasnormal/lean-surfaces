module top;
  logic [7:0] data;
  logic [3:0] index;
  logic [7:0] result;
  initial begin
    data = 8'b01011010;
    index = 4'd1;
    case (data[index + 4'd0])
      data[7]: result = 8'd1;
      data[6]: result = 8'd42;
      default: result = 8'd0;
    endcase
    if (result == 8'd42)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: a9ad3c7d5a964b25301a416a xrun(64) 24.03-s004 2026-10-10T02:18:31Z; PASS.
