/*
:name: struct_array_field_pattern
:description: §7.2/10.9.2 — a fixed unpacked array field inside an unpacked struct accepts an exact positional assignment pattern
:tags: 7.2 10.9.2 unpacked-struct fixed-array assignment-pattern
:type: simulation
*/
module top;
  typedef struct {
    int values [0:1];
  } bucket_t;
  bucket_t bucket;

  initial begin
    bucket.values = '{4, 8};
    if (bucket.values[0] == 4 && bucket.values[1] == 8)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
