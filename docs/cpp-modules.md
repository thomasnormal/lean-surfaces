# C++ modules frontend boundary

The next clause-ladder area is C++ modules and imports ([module]). Its
admission must use the approved Clang AST evidence and retain module identity;
it cannot infer a module from source text or from a filename.

The pinned frontend probe is `harness/cpp_module_probe.py`. It compiles the
fixed C++23 module-unit witness `export module m;` with Clang/LLVM 21.1.8 and
walks the resulting JSON AST structurally. On this toolchain the source
compiles, but the JSON envelope contains no `ModuleDecl` (only the translation
unit and implicit builtin declarations). The probe reports this as a recorded
`REFUSE` boundary and prints the full compiler version. No module semantics are
admitted until the frontend retains a structured module observation or the
approved probe gains an equivalent Clang API supplement.

Run it with:

```sh
python3 harness/cpp_module_probe.py --json /tmp/cpp-module-frontend.json
```
