/*
:name: dynamic_array_new_struct_field_defaults
:description: IEEE 1800-2023 §7.5.1 - new[] on a dynamic array of structs creates elements initialized with struct field defaults.
:tags: 7.5.1 dynamic-array new struct default-initialization
:type: simulation
:spec: IEEE 1800-2023 §7.5.1 defines dynamic-array allocation with new[]; without an initialization expression, each new element is initialized to the default value for its element type.
*/
module top;
  typedef struct {
    int id = 7;
    byte code;
  } item_t;

  item_t dst[];

  initial begin
    dst = new[2];

    if (dst.size() != 2) begin
      $display("FAIL: size=%0d", dst.size());
      $finish;
    end

    if (dst[0].id != 7 || dst[0].code != 0 ||
        dst[1].id != 7 || dst[1].code != 0) begin
      $display("FAIL: dst0={%0d,%0h} dst1={%0d,%0h}",
               dst[0].id, dst[0].code, dst[1].id, dst[1].code);
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
