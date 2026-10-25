/*
:name: queue_empty_pop_struct_default
:description: IEEE 1800-2023 Sections 7.10.2.4 and 7.4.6 -- an empty queue pop returns an unpacked struct's default fields.
:tags: 7.10.2.4 queue pop_front struct default-value
:type: simulation
:spec: IEEE 1800-2023 Section 7.10.2.4 defines pop_front(); Section 7.4.6 defines default initialization of aggregate elements.
*/
module top;
  typedef struct {
    int id;
    bit [3:0] flags;
  } item_t;

  item_t q[$];
  item_t item;

  initial begin
    item.id = 99;
    item.flags = 4'hf;
    item = q.pop_front();

    if (q.size() == 0 && item.id == 0 && item.flags == 4'h0)
      $display("PASS");
    else
      $display("FAIL: size=%0d id=%0d flags=%0h", q.size(), item.id,
               item.flags);
    $finish;
  end
endmodule
