/* A packed-struct array accepts a type-keyed enum field and scalar default. */
module top;
  typedef enum int {IDLE = 1, BUSY = 2} state_t;
  typedef struct packed { state_t state; int raw; } item_t;
  item_t items[0:1];
  initial begin
    items = '{default: '{state_t: BUSY, default: 7}};
    if (items[0].state == BUSY && items[0].raw == 7 &&
        items[1].state == BUSY && items[1].raw == 7)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
