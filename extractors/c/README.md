# C frontend probes

`string_bytes_probe.cpp` is a pinned Clang 21.1.8 AST plugin.  Clang's JSON
dump retains a string literal's source spelling; the plugin records the same
parser node's decoded `StringLiteral::getBytes()` sequence, together with the
source offset and character width.  The C extractor can join these records by
offset without decoding source text.  For ordinary and wide literals the
envelope carries the payload followed by one zero character at that parser
reported width, so the semantic layer receives complete object bytes. The
plugin is an observation tool, not a second C parser or an admitted semantic
layer.

`floating_bits_probe.cpp` is the corresponding parser-native observation for
`FloatingLiteral` nodes.  It records Clang's rounded APFloat bit pattern,
width, source span, and AST type for joining to the envelope.  The probe does
not decode a C spelling in Python or Lean.

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

Build and check the floating-literal probe outside the repository:

```sh
export LEAN_C_FLOATING_BITS_PLUGIN=/outside/the/repo/floating_bits_probe.so
"$LEAN_C_CLANGXX" --no-default-config -std=c++17 -fPIC -shared -fno-rtti \
  -I"$LEAN_C_HEADERS/include" extractors/c/floating_bits_probe.cpp \
  -L"$LEAN_C_LIBS" -Wl,-rpath,"$LEAN_C_LIBS" -Wl,--no-undefined \
  -l:libclang-cpp.so.21.1 -l:libLLVM.so.21.1 -o "$LEAN_C_FLOATING_BITS_PLUGIN"
python3 harness/c_floating_bits_determinism.py --self-test \
  --clang "$LEAN_C_CLANG" --plugin "$LEAN_C_FLOATING_BITS_PLUGIN"
python3 harness/c_floating_bits_determinism.py \
  --clang "$LEAN_C_CLANG" --plugin "$LEAN_C_FLOATING_BITS_PLUGIN" file.c
```

The semantic tier remains loud for escaped and non-ASCII strings until these
records are joined into the C envelope and their exact byte semantics are
priced against the corpus.

`record_layout_probe.cpp` observes Clang's `ASTRecordLayout` for complete
structs and unions: size, alignment, source span, and each field's bit offset
and bit-field width.  It joins records by the parser-provided source span; it
does not interpret a type spelling or serialize an address.  Build and run the
determinism check with the pinned frontend:

The same probe emits `TypeLayout` facts for complete declared object types,
including declarator-shaped function-pointer objects. These are joined by
Clang's exact type string and carried as `type_layouts`; no type-spelling
parser or ABI address model is introduced.

```sh
export LEAN_C_RECORD_LAYOUT_PLUGIN=/outside/the/repo/record_layout_probe.so
"$LEAN_C_CLANGXX" --no-default-config -std=c++17 -fPIC -shared -fno-rtti \
  -I"$LEAN_C_HEADERS/include" extractors/c/record_layout_probe.cpp \
  -L"$LEAN_C_LIBS" -Wl,-rpath,"$LEAN_C_LIBS" -Wl,--no-undefined \
  -l:libclang-cpp.so.21.1 -l:libLLVM.so.21.1 -o "$LEAN_C_RECORD_LAYOUT_PLUGIN"
python3 harness/c_record_layout_determinism.py --self-test \
  --clang "$LEAN_C_CLANG" --plugin "$LEAN_C_RECORD_LAYOUT_PLUGIN"
python3 harness/c_record_layout_determinism.py \
  --clang "$LEAN_C_CLANG" --plugin "$LEAN_C_RECORD_LAYOUT_PLUGIN" file.c
```

To price joins on selected frozen files, keep outputs outside the repository
and restrict the manifest by repeating `--name`:

```sh
python3 harness/c_record_layout_join_price.py \
  --manifest /outside/cache/c1-manifest.json \
  --plugin "$LEAN_C_RECORD_LAYOUT_PLUGIN" --clang "$LEAN_C_CLANG" \
  --out-dir /outside/cache/layout-env \
  --name 20230630-1.c --name pr49123.c
```
