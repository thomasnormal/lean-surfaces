# C frontend probes

`string_bytes_probe.cpp` is a pinned Clang 21.1.8 AST plugin.  Clang's JSON
dump retains a string literal's source spelling; the plugin records the same
parser node's decoded `StringLiteral::getBytes()` sequence, together with the
source offset and character width.  The C extractor can join these records by
offset without decoding source text.  The plugin is an observation tool, not
a second C parser or an admitted semantic layer.

Build it against the matching Clang/LLVM development installation outside the
repository:

```sh
export LEAN_C_CLANGXX=/path/to/clang++
export LEAN_C_HEADERS=/path/to/clang-21.1.8-headers
export LEAN_C_LIBS=/path/to/clang-21.1.8-libraries
export LEAN_C_STRING_BYTES_PLUGIN=/outside/the/repo/string_bytes_probe.so
"$LEAN_C_CLANGXX" --no-default-config -std=c++17 -fPIC -shared -fno-rtti \
  -I"$LEAN_C_HEADERS/include" extractors/c/string_bytes_probe.cpp \
  -L"$LEAN_C_LIBS" -Wl,-rpath,"$LEAN_C_LIBS" -Wl,--no-undefined \
  -l:libclang-cpp.so.21.1 -l:libLLVM.so.21.1 -o "$LEAN_C_STRING_BYTES_PLUGIN"
```

Run the double-run determinism check on a C source accepted by the pinned
frontend:

```sh
python3 harness/c_string_bytes_determinism.py \
  --clang "$LEAN_C_CLANG" --plugin "$LEAN_C_STRING_BYTES_PLUGIN" file.c
```

The semantic tier remains loud for escaped and non-ASCII strings until these
records are joined into the C envelope and their exact byte semantics are
priced against the corpus.
