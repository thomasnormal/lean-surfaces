module top;
  typedef enum logic [1:0] {IDLE = 2'd0, BUSY = 2'd1} state_t;
  state_t state;
  logic [1:0] subject;
  logic [1:0] first_label;
  logic [1:0] second_label;
  logic [3:0] result;
  initial begin
    state = BUSY;
    subject = 2'd2;
    first_label = 2'd1;
    second_label = 2'd2;
    case (subject + 2'd0)
      first_label + 2'd0: result = 4'd1;
      second_label: begin
        case (state)
          IDLE: result = 4'd2;
          BUSY: begin
            subject = 2'd3;
            result = 4'd7;
          end
          default: result = 4'd0;
        endcase
      end
      2'd3: result = 4'd9;
      default: result = 4'd0;
    endcase
    if (result == 4'd7 && subject == 2'd3)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: aca735983234b8b5753efdfe xrun(64) 24.03-s004 2026-10-10T02:18:33Z; PASS.
