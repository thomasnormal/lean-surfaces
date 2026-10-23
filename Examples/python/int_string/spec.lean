import Examples.python.int_string.proof

open LeanModels LeanModels.Python

load_program int_string from "Examples/python/int_string/int_string.json"

set_option maxRecDepth 8192

#py_check int_string.parse_decimal("1_024") = 1024
#py_check int_string.parse_decimal(" \t\n\r\u000b\u000c+1_2_3 \t\n\r\u000b\u000c") = 123
#py_check int_string.parse_decimal("-0_0_0") = 0
#py_check int_string.parse_decimal("+000_007") = 7
#py_check int_string.parse_decimal("9_876_543_210") = 9876543210
#py_check int_string.grouped_offset(-1025) = -1
#py_check int_string.signed_adjustment(2049) = 1
#guard callFunction int_string "parse_decimal"
  #[.str (String.ofList (List.replicate 640 '0'))] 4096 matches .ok (.int 0)

#py_check int_string.parse_decimal("") raises
  (.valueError "invalid literal for int() with base 10: ''")
#py_check int_string.parse_decimal(" \t\n\r\u000b\u000c") raises
  (.valueError "invalid literal for int() with base 10: ' \\t\\n\\r\\x0b\\x0c'")
#py_check int_string.parse_decimal("+") raises
  (.valueError "invalid literal for int() with base 10: '+'")
#py_check int_string.parse_decimal("- 3") raises
  (.valueError "invalid literal for int() with base 10: '- 3'")
#py_check int_string.parse_decimal("1__2") raises
  (.valueError "invalid literal for int() with base 10: '1__2'")
#py_check int_string.parse_decimal("_12") raises
  (.valueError "invalid literal for int() with base 10: '_12'")
#py_check int_string.parse_decimal("12_") raises
  (.valueError "invalid literal for int() with base 10: '12_'")
#py_check int_string.parse_decimal("+_1") raises
  (.valueError "invalid literal for int() with base 10: '+_1'")
#py_check int_string.parse_decimal("1 _2") raises
  (.valueError "invalid literal for int() with base 10: '1 _2'")
#py_check int_string.parse_decimal("12x3") raises
  (.valueError "invalid literal for int() with base 10: '12x3'")
#py_check int_string.parse_decimal("0x10") raises
  (.valueError "invalid literal for int() with base 10: '0x10'")
#py_check int_string.parse_decimal("1\u0000") raises
  (.valueError "invalid literal for int() with base 10: '1\\x00'")
#py_check int_string.parse_decimal("a'b") raises
  (.valueError "invalid literal for int() with base 10: \"a'b\"")
#py_check int_string.parse_decimal("a\"b") raises
  (.valueError "invalid literal for int() with base 10: 'a\"b'")
#py_check int_string.parse_decimal("a'\"b") raises
  (.valueError "invalid literal for int() with base 10: 'a\\'\"b'")
#py_check int_string.parse_decimal("1\\2") raises
  (.valueError "invalid literal for int() with base 10: '1\\\\2'")
#py_check int_string.parse_decimal("1\n2") raises
  (.valueError "invalid literal for int() with base 10: '1\\n2'")
#py_check int_string.long_invalid() raises
  (.valueError ("invalid literal for int() with base 10: '" ++
    String.ofList (List.replicate 199 'x')))
#py_check int_string.long_escaped_invalid() raises
  (.valueError ("invalid literal for int() with base 10: '" ++
    String.join (List.replicate 49 "\\x00") ++ "\\x0"))

#guard callFunction int_string "parse_decimal" #[.str "٣"] 4096 matches .unsupported _
#guard callFunction int_string "parse_decimal" #[.str "１２"] 4096 matches .unsupported _
#guard callFunction int_string "parse_decimal" #[.str "\u00a01"] 4096 matches .unsupported _
#guard callFunction int_string "parse_decimal" #[.str "é"] 4096 matches .unsupported _
#py_check int_string.explicit_base("12", 10) = 12
#py_check int_string.explicit_base("0xff", 0) = 255
#py_check int_string.explicit_base("-0B_1_0", 0) = -2
#py_check int_string.explicit_base("0_0_0", 0) = 0
#py_check int_string.explicit_base("0b10", 16) = 2832
#py_check int_string.explicit_base("Zz", 36) = 1295
#py_check int_string.explicit_base((#[102, 102] : PyBytes), 16) = 255
#py_check int_string.keyword_base("ff", 16) = 255
#py_check int_string.hex_offset(-255) = 0
#py_check int_string.explicit_base("010", 0) raises
  (.valueError "invalid literal for int() with base 0: '010'")
#py_check int_string.explicit_base("0x__1", 0) raises
  (.valueError "invalid literal for int() with base 0: '0x__1'")
#py_check int_string.explicit_base("10", 1) raises
  (.valueError "int() base must be >= 2 and <= 36, or 0")
#py_check int_string.explicit_base("10", "2") raises
  (.typeError "'str' object cannot be interpreted as an integer")
#py_check int_string.explicit_base(12, 10) raises
  (.typeError "int() can't convert non-string with explicit base")
#py_check int_string.missing_string(16) raises (.typeError "int() missing string argument")
#py_check int_string.duplicate_base("ff", 16) raises
  (.typeError "int() takes at most 2 arguments (3 given)")
#py_check int_string.too_many("ff", 16) raises
  (.typeError "int() takes at most 2 arguments (3 given)")
#py_check int_string.total_before_keyword() raises
  (.typeError "int() takes at most 2 arguments (3 given)")
#py_check int_string.too_many_keywords() raises
  (.typeError "int() takes at most 2 keyword arguments (3 given)")
#py_check int_string.unknown_keyword(true) raises
  (.typeError "'other' is an invalid keyword argument for int()")
#py_check int_string.unknown_keyword(false) raises
  (.typeError "'other' is an invalid keyword argument for int()")
#py_check int_string.positional_string_only() raises
  (.typeError "'x' is an invalid keyword argument for int()")
#py_check int_string.argument_effects() = (Val.tuple #[.int 255, .list #[.int 1, .int 2]])
#py_check int_string.arity_effects() = (Val.list #[.int 1, .int 2, .int 3])
#py_check int_string.conversion_effects() = (Val.list #[.int 1, .int 2])
#py_check int_string.keyword_value_error() raises .zeroDivisionError
#py_check int_string.arity_value_error() raises .zeroDivisionError
#guard callFunction int_string "parse_decimal"
  #[.str (String.ofList (List.replicate 1025 '0'))] 4096 matches .unsupported _

theorem grouped_offset_total (offset : PyInt) :
    int_string.grouped_offset(offset) ==> 1024 + offset := by proofs

theorem signed_adjustment_total (offset : PyInt) :
    int_string.signed_adjustment(offset) ==> offset - 2048 := by proofs

theorem hex_offset_total (offset : PyInt) :
    int_string.hex_offset(offset) ==> 255 + offset := by proofs

theorem grouped_offset_result (offset result : PyInt)
    (run : int_string.grouped_offset(offset) ⇓ result) : result = 1024 + offset := by proofs
