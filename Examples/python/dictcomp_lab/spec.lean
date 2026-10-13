import LeanModels.Python

open LeanModels LeanModels.Python

load_program dictcomp_lab from "Examples/python/dictcomp_lab/dictcomp_lab.json"

#py_check dictcomp_lab.from_range(5, 3) = (Val.tuple #[.int 5, .int 9])
#py_check dictcomp_lab.from_range(2, 7) = (Val.tuple #[.int 2, .int (-1)])
#py_check dictcomp_lab.duplicate_keys(5) = (Val.tuple #[.int 4, .int 3])
#py_check dictcomp_lab.bad_pair() raises
  (.typeError "cannot convert dictionary update sequence element #0 to a sequence")
#py_check dictcomp_lab.bad_length() raises
  (.valueError "dictionary update sequence element #0 has length 1; 2 is required")
#py_check dictcomp_lab.unhashable_key() raises
  (.typeError "unhashable type: 'list'")
