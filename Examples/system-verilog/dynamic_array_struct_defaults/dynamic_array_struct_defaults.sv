/*
:name: dynamic_array_new_default_inits_struct_elements
:description: IEEE 1800-2023 §7.5.1 p.159 -- dynamic-array new without an initialization expression initializes new elements to the default value for their element type.
:tags: 7.5.1 dynamic-array new default-initialization struct
:type: simulation
:spec: IEEE 1800-2023 §7.5.1 p.159 states that if a dynamic-array new constructor has no initialization expression, elements are initialized to the default value for their type.
*/
module top;
  typedef struct {
    int count;
    bit [3:0] tag;
  } item_t;

  item_t items[];

  initial begin
    items = new[2];

    if (items.size() != 2) begin
      $display("FAIL: size=%0d", items.size());
      $finish;
    end

    if (items[0].count != 0 || items[0].tag !== 4'h0 ||
        items[1].count != 0 || items[1].tag !== 4'h0) begin
      $display("FAIL: items[0]={%0d,%h} items[1]={%0d,%h}",
               items[0].count, items[0].tag, items[1].count, items[1].tag);
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
