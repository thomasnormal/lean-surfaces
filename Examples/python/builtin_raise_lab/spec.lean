import LeanModels.Python.Script

import Examples.python.builtin_raise_lab.proof

open LeanModels LeanModels.Python

load_program builtin_raise_lab from "Examples/python/builtin_raise_lab/builtin_raise_lab.json"
load_program builtin_raise_namedtuple from "Examples/python/builtin_raise_lab/builtin_raise_namedtuple.json"

#py_check builtin_raise_lab.raise_BaseException() raises (.builtinException "BaseException")

#py_check builtin_raise_lab.catch_BaseException(23) = 23

#py_check builtin_raise_lab.raise_Exception() raises (.builtinException "Exception")

#py_check builtin_raise_lab.catch_Exception(23) = 23

#py_check builtin_raise_lab.raise_ArithmeticError() raises (.builtinException "ArithmeticError")

#py_check builtin_raise_lab.catch_ArithmeticError(23) = 23

#py_check builtin_raise_lab.raise_LookupError() raises (.builtinException "LookupError")

#py_check builtin_raise_lab.catch_LookupError(23) = 23

#py_check builtin_raise_lab.raise_TypeError() raises (.builtinException "TypeError")

#py_check builtin_raise_lab.catch_TypeError(23) = 23

#py_check builtin_raise_lab.raise_NameError() raises (.builtinException "NameError")

#py_check builtin_raise_lab.catch_NameError(23) = 23

#py_check builtin_raise_lab.raise_ZeroDivisionError() raises (.builtinException "ZeroDivisionError")

#py_check builtin_raise_lab.catch_ZeroDivisionError(23) = 23

#py_check builtin_raise_lab.raise_OverflowError() raises (.builtinException "OverflowError")

#py_check builtin_raise_lab.catch_OverflowError(23) = 23

#py_check builtin_raise_lab.raise_IndexError() raises (.builtinException "IndexError")

#py_check builtin_raise_lab.catch_IndexError(23) = 23

#py_check builtin_raise_lab.raise_ValueError() raises (.builtinException "ValueError")

#py_check builtin_raise_lab.catch_ValueError(23) = 23

#py_check builtin_raise_lab.raise_KeyError() raises (.builtinException "KeyError")

#py_check builtin_raise_lab.catch_KeyError(23) = 23

#py_check builtin_raise_lab.raise_RuntimeError() raises (.builtinException "RuntimeError")

#py_check builtin_raise_lab.catch_RuntimeError(23) = 23

#py_check builtin_raise_lab.raise_RecursionError() raises (.builtinException "RecursionError")

#py_check builtin_raise_lab.catch_RecursionError(23) = 23

#py_check builtin_raise_lab.raise_AttributeError() raises (.builtinException "AttributeError")

#py_check builtin_raise_lab.catch_AttributeError(23) = 23

#py_check builtin_raise_lab.raise_AssertionError() raises (.builtinException "AssertionError")

#py_check builtin_raise_lab.catch_AssertionError(23) = 23

#py_check builtin_raise_lab.raise_StopIteration() raises (.builtinException "StopIteration")

#py_check builtin_raise_lab.catch_StopIteration(23) = 23

#py_check builtin_raise_lab.raise_ImportError() raises (.builtinException "ImportError")

#py_check builtin_raise_lab.catch_ImportError(23) = 23

#py_check builtin_raise_lab.raise_ModuleNotFoundError() raises
  (.builtinException "ModuleNotFoundError")

#py_check builtin_raise_lab.catch_ModuleNotFoundError(23) = 23

#py_check builtin_raise_lab.raise_EnvironmentError() raises
  (.builtinException "OSError")

#py_check builtin_raise_lab.catch_EnvironmentError(23) = 23

#py_check builtin_raise_lab.raise_IOError() raises (.builtinException "OSError")

#py_check builtin_raise_lab.catch_IOError(23) = 23

#py_check builtin_raise_lab.raise_StopAsyncIteration() raises
  (.builtinException "StopAsyncIteration")

#py_check builtin_raise_lab.catch_StopAsyncIteration(23) = 23

#py_check builtin_raise_lab.raise_Warning() raises
  (.builtinException "Warning")

#py_check builtin_raise_lab.catch_Warning(23) = 23

#py_check builtin_raise_lab.raise_UnicodeError() raises
  (.builtinException "UnicodeError")

#py_check builtin_raise_lab.catch_UnicodeError(23) = 23

#py_check builtin_raise_lab.raise_UnicodeWarning() raises
  (.builtinException "UnicodeWarning")

#py_check builtin_raise_lab.catch_UnicodeWarning(23) = 23

#py_check builtin_raise_lab.raise_UserWarning() raises
  (.builtinException "UserWarning")

#py_check builtin_raise_lab.catch_UserWarning(23) = 23

#py_check builtin_raise_lab.base_not_exception() = 2

#py_check builtin_raise_lab.wrong_sibling() = 2

#py_check builtin_raise_lab.retained_state() = (Val.list #[.int 0, .int 1, .int 2])

#py_check builtin_raise_lab.through_call() = 9

#py_check builtin_raise_lab.generator_closed() = 17

#py_check builtin_raise_lab.generator_escape() raises (.runtimeError "generator raised StopIteration")

#py_check builtin_raise_lab.exhaustion_escape() raises (.runtimeError "generator raised StopIteration")

#py_check builtin_raise_lab.caught_inside_generator() = 5

#py_check builtin_raise_namedtuple.raise_value_error() raises
  (.typeError "exceptions must derive from BaseException")

#py_check builtin_raise_namedtuple.raise_stop_iteration() raises
  (.typeError "exceptions must derive from BaseException")

#py_check builtin_raise_namedtuple.raise_record() raises
  (.typeError "exceptions must derive from BaseException")

#py_check builtin_raise_namedtuple.catch_shadow(23) = 23

#py_check builtin_raise_namedtuple.generator_closed() = 17

#py_check builtin_raise_namedtuple.generator_escape() raises
  (.typeError "exceptions must derive from BaseException")

#py_check builtin_raise_namedtuple.invalid_handler() raises
  (.typeError "catching classes that do not inherit from BaseException is not allowed")

#py_check builtin_raise_namedtuple.handler_success(23) = 23

#py_check builtin_raise_namedtuple.handler_retained_state() =
  (Val.list #[.int 0, .int 1, .int 3])

#guard callFunction builtin_raise_lab "late_shadow" #[] 4096 matches
  .exn (.unboundLocalError "ValueError")

#py_check builtin_raise_lab.raised_instance() raises (.builtinException "ValueError")

#py_check builtin_raise_lab.chained() raises (.builtinException "ValueError")

#py_check builtin_raise_lab.unsupported_class() raises (.builtinException "OSError")

#py_check builtin_raise_lab.parameter_shadow(1) raises
  (.typeError "exceptions must derive from BaseException")

theorem catch_value_error_total (value : PyInt) :
    builtin_raise_lab.catch_ValueError(value) ==> value := by proofs

#print axioms catch_value_error_total
