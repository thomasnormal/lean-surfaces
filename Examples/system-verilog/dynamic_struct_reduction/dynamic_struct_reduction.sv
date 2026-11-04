/* A finite dynamic array of structs can reduce one integral field. */
module top;
  typedef struct { int id; int weight; } item_t;
  item_t items[];
  int total;
  initial begin
    items = new[3];
    items[0] = '{id:1, weight:10};
    items[1] = '{id:2, weight:20};
    items[2] = '{id:3, weight:30};
    total = items.sum() with (item.weight);
    if (total === 60)
      $display("PASS");
    else
      $display("FAIL %0d", total);
    $finish;
  end
endmodule
