# C++ modules frontend boundary

The next clause-ladder area is C++ modules and imports ([module]). Its
admission must use the approved Clang AST evidence and retain module identity;
it cannot infer a module from source text or from a filename.

The pinned frontend probe is `harness/cpp_module_probe.py`. It precompiles a
fixed C++23 module unit and compiles an importer with Clang/LLVM 21.1.8, then
walks the importer JSON AST structurally. The envelope contains an `ImportDecl`
but no `ModuleDecl`, module name, or imported-module declaration handle. The
probe reports this as a recorded `REFUSE` boundary and prints the full compiler
version. No module semantics are admitted until the frontend retains structured
module identity or the approved probe gains an equivalent Clang API supplement.

Run it with:

```sh
python3 harness/cpp_module_probe.py --json /tmp/cpp-module-frontend.json
```
