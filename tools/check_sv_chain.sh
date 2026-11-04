#!/usr/bin/env bash
# tools/check_sv_chain.sh — build the SystemVerilog COMB CHAIN and its Examples, and fail if either breaks.
#
# WHY.  Off a GitHub runner nothing builds the comb chain (`LeanModels/Sv/Comb*.lean`, the `sv_comb` tactics) as a unit:
#   * `lake build LeanModels` (the root library) reaches NONE of it — `LeanModels.lean` imports the core Sv chain
#     (Tests, SelfCheck, Param, Ingest2, ...), and the comb modules are reachable only through `Examples/system-verilog`;
#   * `tools/ci.sh` builds those Examples file by file, but ONLY on a GitHub runner (`GITHUB_ACTIONS=true`); on any other
#     host it prints `lake-build SKIPPED on non-CI host` (and `--require-build` turns that into a failure);
#   * `tools/triad.sh --classify` scopes a landing to the TOUCHED modules (`LeanModels.Sv.<Touched>`), and the Sv tier has
#     no root module to bring their dependents along, so a change to a core file (a new constructor, a renamed lemma) that
#     broke a comb module three imports away was not built by the landing that caused it.
# This broke the merged tree twice on 2026-11-01 (a new `PStmt` constructor left four non-exhaustive matches in
# `CombProc.lean`; stale oleans hid it until a chain build). This script is that chain build, in one command, and
# `--dependents` is what closes the local landing path: triad.sh adds its answer to the landing's one `lake build`.
#
# WHAT IT BUILDS (two `lake build` invocations, so a failure says which half broke, and each is one slot acquisition):
#   1. the LIBRARY group: every `LeanModels/Sv/Comb*.lean` module and `LeanModels.Sv.PinAxioms` (found by glob, so a new
#      comb module is covered the day it lands), plus two roots whose modules nothing in `LeanModels` imports (their only
#      importers are `svgolf/design` drafts): `LeanModels.Sv.ObsLib` (the observation lane: Observe*, CycleMachine,
#      REdgeRun2, FlatMemRun2, Contract*) and `LeanModels.Sv.Kernel` (E: every `Kernel/*` module and `Comb2Fuel`),
#      `LeanModels.Sv.XMono` (the width-parametric monotonicity theorems; imported by nothing), and
#      `LeanModels.Sv.SeqFamily` and `LeanModels.Sv.SeqProfile` (the clocked-family lemmas; their only importers are svGolf's
#      clocked references);
#   2. the EXAMPLES group: every `Examples/system-verilog/**/*.lean` file that imports a `LeanModels.Sv.Comb*` module, or
#      (to a fixpoint) imports such an Example (found by grep; `sem2/` is the semantic-agreement lane, built by its own
#      gates, and is left out). Everything they import comes along as a dependency.
# The module list is printed first. A failing library group skips the Examples (they would fail through it).
#
# WHAT `--dependents` PRINTS.  One per line, in `--list` order, exactly the chain modules that transitively import the
# module of any given `LeanModels/Sv/*.lean` path, and nothing else. Only the ANSWER is limited to the chain: the walk reads
# every `.lean` under LeanModels and Examples, because a path can run through a non-Comb module, another tier or `sem2/`. A
# module is not its own dependent. A path outside LeanModels/Sv, or a leaf nothing imports, prints nothing and exits 0. A
# deleted file still has importers, so a path need not exist. Runs no Lean.
#
# SLOT DISCIPLINE.  With `LEANSLOT` set (the path of a slot wrapper such as the scratchpad's `leanslot.sh`: it takes a
# FIFO ticket, holds one machine-wide slot, and runs the command under `LEAN_NUM_THREADS=2` and `nice 19`), each
# `lake build` runs as `"$LEANSLOT" lake build ...`. Without it, plain `nice -n 19 lake build` with
# `LEAN_NUM_THREADS` defaulting to 2 — on a machine where A11 applies (docs/family-architecture.md §7.1), take a
# ticket first (`tools/triad.sh`) or set `LEANSLOT`. `SVGOLF_LEAN_WRAP` is unset: an outer wrapper that re-takes the
# slot inside a slot deadlocks.
#
# USAGE      bash tools/check_sv_chain.sh              build; exit 0 only if both groups build
#            bash tools/check_sv_chain.sh --list       print the modules, run nothing
#            bash tools/check_sv_chain.sh --dependents PATH...  print the chain modules importing those files, run nothing
#            bash tools/check_sv_chain.sh --self-test  the logic against a stubbed `lake` and slot (NO Lean is run)
# EXIT       0 built; 1 a group failed to build; 2 usage error, no `lake`, or `--dependents` could not read the tree.
set -u
cd "$(dirname "$0")/.."

# ---------------------------------------------------------------- the module lists
lib_modules() {
  { for f in LeanModels/Sv/Comb*.lean; do [ -e "$f" ] && basename "$f" .lean; done; echo PinAxioms; echo ObsLib; echo Kernel; echo XMono; echo SeqFamily; echo SeqProfile; } |
    sort -u | sed 's/^/LeanModels.Sv./'
}

# The comb Examples: every Examples/system-verilog file (outside sem2/) that imports a `LeanModels.Sv.Comb*` module, and,
# to a fixpoint, every file that imports one already chosen (`comb_alias`, `neg/comb_neg` and `ripple_step/comb_proof` import
# only other Examples).
example_files() {
  local sel next pats
  sel="$(grep -rl --include='*.lean' '^import LeanModels\.Sv\.Comb' Examples/system-verilog 2>/dev/null |
    grep -v '^Examples/system-verilog/sem2/' | sort -u)"
  pats="$(mktemp "${TMPDIR:-/tmp}/sv-chain-pats.XXXXXX")" || return 2
  while :; do
    printf '%s\n' "$sel" | sed -e 's/\.lean$//' -e 's#/#.#g' -e 's/system-verilog/«system-verilog»/' -e 's/^/import /' > "$pats"
    next="$( { printf '%s\n' "$sel"
               grep -rlxF --include='*.lean' -f "$pats" Examples/system-verilog 2>/dev/null |
                 grep -v '^Examples/system-verilog/sem2/'; } | sort -u)"
    [ "$next" = "$sel" ] && break
    sel="$next"
  done
  rm -f "$pats"
  printf '%s\n' "$sel"
}

example_modules() {
  example_files | sed -e 's/\.lean$//' -e 's#/#.#g' -e 's/system-verilog/«system-verilog»/'
}

# Fill the global arrays LIB and EX (bash 3.2 has no mapfile).
collect() {
  LIB=(); EX=()
  local m
  while IFS= read -r m; do [ -n "$m" ] && LIB+=("$m"); done < <(lib_modules)
  while IFS= read -r m; do [ -n "$m" ] && EX+=("$m"); done < <(example_modules)
}

print_list() {
  echo "=== [sv-chain] library group (${#LIB[@]} modules)"
  printf '    %s\n' "${LIB[@]}"
  echo "=== [sv-chain] examples group (${#EX[@]} modules)"
  printf '    %s\n' "${EX[@]}"
}

# Refuse an empty group rather than expand it: `"${EX[@]}"` on an empty array is an error under `set -u` on bash 3.2, and
# "no comb Examples" is a wrong checkout, not an answer.
have_chain() {
  [ "${#LIB[@]}" -gt 0 ] && [ "${#EX[@]}" -gt 0 ] && return 0
  echo "check_sv_chain: found no comb modules (run it from a checkout with LeanModels/Sv and Examples/system-verilog)" >&2
  return 2
}

# ---------------------------------------------------------------- what a touched Sv file can break
# Every import in the tree, as `<importer> <imported> ` with plain dotted names. The trailing space is what lets a fixed
# ` M ` match the imported column whole. Guillemets go on both sides, so the walk needs no table of hyphenated directories.
# `public`, `meta` and `all` are Lean's own grammar (Lean/Parser/Module.lean); a missed spelling would be a silent gap.
# The operands' trailing slashes matter: `tools/ci.sh` runs self-tests in a view where both are symlinks, and BSD `grep -r`
# skips a bare symlink operand (0 of 1661 imports read, measured) where GNU grep follows it.
import_edges() {
  grep -rE --include='*.lean' '^[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]' LeanModels/ Examples/ 2>/dev/null |
    sed -E -e 's/«//g' -e 's/»//g' -e 's#//*#.#g' \
      -e 's/^([^:]*)\.lean:[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+(all[[:space:]]+)?([^[:space:]]+).*$/\1 \5 /'
}

union() { printf '%s\n' "$@" | grep . | sort -u; }

# `example_files`' fixpoint, run backwards. It reads the tree once, into the table above, and each round greps for the
# modules the last round found and no others: BSD grep is slow per pattern, and an import chain here is many rounds deep.
dependents() {
  local p seeds="" edges sel front found deps="" pats rc
  for p in "$@"; do
    p="${p#./}"
    case "$p" in LeanModels/Sv/*.lean) seeds="$seeds${p%.lean}
" ;; esac
  done
  [ -n "$seeds" ] || return 0
  # A search that did not happen must not read as "nothing imports it": that is the gap again, from the other side.
  edges="$(import_edges)"
  [ -n "$edges" ] || { echo "check_sv_chain: read no imports under LeanModels and Examples" >&2; return 2; }
  sel="$(printf '%s' "$seeds" | tr / . | sort -u)"
  front="$sel"
  pats="$(mktemp "${TMPDIR:-/tmp}/sv-chain-deps.XXXXXX")" || return 2
  while [ -n "$front" ]; do
    printf '%s\n' "$front" | sed 's/.*/ & /' > "$pats"
    found="$(printf '%s\n' "$edges" | grep -F -f "$pats" | cut -d' ' -f1 | sort -u)"
    printf '%s\n' "$sel" > "$pats"
    front="$(printf '%s\n' "$found" | grep -vxF -f "$pats")"
    # `deps` keeps every importer and `sel` also keeps the seeds, so a seed is an answer only if it imports another seed
    # or something they reach: a module is not its own dependent.
    deps="$(union "$deps" "$found")"
    sel="$(union "$sel" "$front")"
  done
  [ -n "$deps" ] || { rm -f "$pats"; return 0; }
  printf '%s\n' "$deps" | sed 's/^Examples\.system-verilog\./Examples.«system-verilog»./' > "$pats"
  collect
  have_chain || { rm -f "$pats"; return 2; }
  printf '%s\n' "${LIB[@]}" "${EX[@]}" | grep -xF -f "$pats"
  rc=$?
  rm -f "$pats"
  [ "$rc" -le 1 ] || return 2      # 1 is grep's "no match": dependents exist, and none of them is in the chain
  return 0
}

# ---------------------------------------------------------------- one lake build, through the slot when there is one
run_lake() {
  unset SVGOLF_LEAN_WRAP
  if [ -n "${LEANSLOT:-}" ]; then
    "$LEANSLOT" lake build "$@"
  else
    LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" nice -n 19 lake build "$@"
  fi
}

build_all() {
  command -v lake >/dev/null 2>&1 || { echo "check_sv_chain: no \`lake\` on PATH" >&2; return 2; }
  collect
  have_chain || return 2
  print_list
  echo "=== [sv-chain] lake build: library group"
  if ! run_lake "${LIB[@]}"; then
    echo "=== [sv-chain] FAILED: the library group (the Examples were not attempted)" >&2
    return 1
  fi
  echo "=== [sv-chain] lake build: examples group"
  if ! run_lake "${EX[@]}"; then
    echo "=== [sv-chain] FAILED: the examples group" >&2
    return 1
  fi
  echo "=== [sv-chain] OK: ${#LIB[@]} library modules and ${#EX[@]} examples built"
  return 0
}

# ---------------------------------------------------------------- the self-test: a stubbed lake and slot, no Lean
self_test() {
  local tmp ok=0 bad=0 rc out
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/sv-chain-st.XXXXXX")" || return 2
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }
  # `lake` records its arguments and fails when STUB_FAIL names the group it is asked to build
  cat > "$tmp/lake" <<'STUB'
#!/usr/bin/env bash
echo "lake $*" >> "$STUB_LOG"
case "$*" in
  *LeanModels.Sv.CombLib*) [ "${STUB_FAIL:-}" = lib ] && exit 1 ;;
  *) [ "${STUB_FAIL:-}" = ex ] && exit 1 ;;
esac
exit 0
STUB
  # the slot wrapper records that it ran, then runs the command it was given
  cat > "$tmp/slot" <<'STUB'
#!/usr/bin/env bash
echo "slot" >> "$STUB_LOG"
exec "$@"
STUB
  chmod +x "$tmp/lake" "$tmp/slot"
  local self="$PWD/tools/check_sv_chain.sh"
  export STUB_LOG="$tmp/log"
  : > "$STUB_LOG"; out="$(PATH="$tmp:$PATH" env -u LEANSLOT bash "$self" --list 2>&1)"; rc=$?
  check "--list exits 0" "$rc" 0
  check "--list names a library module" "$(printf '%s' "$out" | grep -c 'LeanModels.Sv.CombLib')" 1
  check "--list names an example module" "$(printf '%s' "$out" | grep -c '«system-verilog».comb_ops.comb_proof')" 1
  check "--list names no sem2 module" "$(printf '%s' "$out" | grep -c 'sem2')" 0
  check "--list runs no lake" "$(grep -c '^lake' "$STUB_LOG")" 0
  : > "$STUB_LOG"; PATH="$tmp:$PATH" env -u LEANSLOT bash "$self" >/dev/null 2>&1; rc=$?
  check "no slot: exits 0 when lake succeeds" "$rc" 0
  check "no slot: two lake builds" "$(grep -c '^lake build' "$STUB_LOG")" 2
  check "no slot: the slot is not used" "$(grep -c '^slot' "$STUB_LOG")" 0
  : > "$STUB_LOG"; PATH="$tmp:$PATH" LEANSLOT="$tmp/slot" bash "$self" >/dev/null 2>&1; rc=$?
  check "slot: exits 0 when lake succeeds" "$rc" 0
  check "slot: each build goes through the slot" "$(grep -c '^slot' "$STUB_LOG")" 2
  : > "$STUB_LOG"; PATH="$tmp:$PATH" env -u LEANSLOT STUB_FAIL=lib bash "$self" >/dev/null 2>&1; rc=$?
  check "a failing library group exits 1" "$rc" 1
  check "  ...and the examples are not attempted" "$(grep -c '^lake build' "$STUB_LOG")" 1
  : > "$STUB_LOG"; PATH="$tmp:$PATH" env -u LEANSLOT STUB_FAIL=ex bash "$self" >/dev/null 2>&1; rc=$?
  check "a failing examples group exits 1" "$rc" 1
  out="$(bash "$self" --bogus 2>&1)"; rc=$?
  check "an unknown argument exits 2" "$rc" 2

  # --dependents, over a fixture tree: the script roots itself at its own location, so a copy of it walks that tree.
  # Obs is the core file: Obs -> Foo (not Comb) -> CombBar -> PinAxioms and the Examples.
  local tree="$tmp/tree"
  mk() { mkdir -p "$(dirname "$tree/$1")"; printf '%s\n' "$2" > "$tree/$1"; }
  mkdir -p "$tree/tools"; cp "$self" "$tree/tools/check_sv_chain.sh"
  mk LeanModels/Sv/Obs.lean        '-- imports nothing'
  mk LeanModels/Sv/Foo.lean        'import LeanModels.Sv.Obs'
  mk LeanModels/Sv/CombBar.lean    'import LeanModels.Sv.Foo'
  mk LeanModels/Sv/PinAxioms.lean  'import LeanModels.Sv.CombBar'
  mk LeanModels/Sv/CombOff.lean    '-- import LeanModels.Sv.Obs'
  mk LeanModels/Sv/Leaf.lean       'import LeanModels.Sv.Obs'
  mk LeanModels/Sv/Solo.lean       'import LeanModels.Sv.Obs'
  mk LeanModels/Sv/Tests.lean      'import LeanModels.Sv.Solo'
  mk LeanModels/Sv/Core2.lean      '-- imports nothing'
  mk LeanModels/Other/Bridge.lean  'import LeanModels.Sv.Core2'
  mk LeanModels/Sv/CombVia.lean    'import LeanModels.Other.Bridge'
  mk LeanModels/Sv/Tol.lean        '-- imports nothing'
  mk LeanModels/Sv/CombTrail.lean  'import LeanModels.Sv.Tol  -- a trailing comment'
  mk LeanModels/Sv/CombPub.lean    'public import LeanModels.Sv.Tol'
  mk LeanModels/Sv/CombGone.lean   'import LeanModels.Sv.Gone'
  mk LeanModels/Sv/Deep.lean       '-- imports nothing'
  mk Examples/system-verilog/ex/proof.lean 'import LeanModels.Sv.CombBar'
  mk Examples/system-verilog/ex/top.lean   'import Examples.«system-verilog».ex.proof'
  mk Examples/system-verilog/sem2/s.lean   'import LeanModels.Sv.CombBar'
  mk Examples/system-verilog/sem2/mid.lean 'import LeanModels.Sv.Deep'
  printf 'import LeanModels.Sv.CombBar\nimport Examples.«system-verilog».sem2.mid\n' > "$tree/Examples/system-verilog/ex/via.lean"
  dep() { out="$(cd / && PATH="$tmp:$PATH" env -u LEANSLOT bash "$tree/tools/check_sv_chain.sh" --dependents "$@" 2>/dev/null)"; rc=$?; out="$(printf '%s' "$out" | tr '\n' ' ')"; }
  local ex='Examples.«system-verilog».ex'
  : > "$STUB_LOG"; dep LeanModels/Sv/Obs.lean
  check "--dependents walks through a non-Comb module, and to the Examples" "$out" "LeanModels.Sv.CombBar LeanModels.Sv.PinAxioms $ex.proof $ex.top $ex.via"
  check "  ...exits 0" "$rc" 0
  check "  ...and runs no lake" "$(grep -c '^lake' "$STUB_LOG")" 0
  dep LeanModels/Sv/CombBar.lean
  check "--dependents: a module is not its own dependent" "$out" "LeanModels.Sv.PinAxioms $ex.proof $ex.top $ex.via"
  dep LeanModels/Sv/CombBar.lean LeanModels/Sv/Obs.lean
  check "--dependents: a seed importing another seed IS one" "$out" "LeanModels.Sv.CombBar LeanModels.Sv.PinAxioms $ex.proof $ex.top $ex.via"
  dep LeanModels/Sv/Leaf.lean
  check "--dependents: a leaf nothing imports prints nothing" "$out" ""
  check "  ...and exits 0" "$rc" 0
  dep LeanModels/Sv/Solo.lean
  check "--dependents: dependents outside the chain are not printed" "$out" ""
  check "  ...and exit 0" "$rc" 0
  dep LeanModels/Python/Surface.lean docs/a.md Examples/system-verilog/ex/proof.lean LeanModels/Sv/notes.md
  check "--dependents: non-Sv paths print nothing" "$out" ""
  check "  ...and exit 0" "$rc" 0
  dep LeanModels/Sv/Core2.lean
  check "--dependents walks through another tier" "$out" "LeanModels.Sv.CombVia"
  dep LeanModels/Sv/Deep.lean
  check "--dependents walks through sem2, and prints none of it" "$out" "$ex.via"
  dep LeanModels/Sv/Tol.lean
  check "--dependents reads a trailing comment and \`public import\`" "$out" "LeanModels.Sv.CombPub LeanModels.Sv.CombTrail"
  dep LeanModels/Sv/Gone.lean
  check "--dependents: a deleted file still has importers" "$out" "LeanModels.Sv.CombGone"
  dep ./LeanModels/Sv/Core2.lean
  check "--dependents accepts a leading ./" "$out" "LeanModels.Sv.CombVia"
  # The shape of tools/ci.sh's self-test view: the top-level directories are symlinks.
  local linked="$tmp/linked"; mkdir -p "$linked/tools"; cp "$self" "$linked/tools/check_sv_chain.sh"
  ln -s "$tree/LeanModels" "$linked/LeanModels"; ln -s "$tree/Examples" "$linked/Examples"
  out="$(bash "$linked/tools/check_sv_chain.sh" --dependents LeanModels/Sv/Core2.lean)"
  check "--dependents reads a tree whose top directories are symlinks" "$out" "LeanModels.Sv.CombVia"
  out="$(bash "$tree/tools/check_sv_chain.sh" --dependents 2>&1)"; rc=$?
  check "--dependents with no path is a usage error" "$rc" 2
  # A tree it could not read is not an empty answer: triad.sh would take that for "nothing to build".
  local empty="$tmp/empty"; mkdir -p "$empty/tools"; cp "$self" "$empty/tools/check_sv_chain.sh"
  out="$(bash "$empty/tools/check_sv_chain.sh" --dependents LeanModels/Sv/Obs.lean 2>&1)"; rc=$?
  check "--dependents on a tree with no imports refuses" "$rc" 2
  out="$(bash "$empty/tools/check_sv_chain.sh" --dependents docs/a.md 2>&1)"; rc=$?
  check "  ...while a non-Sv path never asks the tree" "$rc" 0
  # THE INCIDENT, on the real tree: `PStmt` lives in Param.lean, and CombProc is what its new constructor broke.
  out="$(bash "$self" --dependents LeanModels/Sv/Param.lean)"; rc=$?
  check "the real tree: Param.lean reaches CombProc" "$(printf '%s\n' "$out" | grep -cx 'LeanModels.Sv.CombProc')" 1
  check "  ...and every name it prints is one \`--list\` prints" "$(printf '%s\n' "$out" | grep -vxF -f <(bash "$self" --list | sed 's/^    //') | grep -c .)" 0
  rm -rf "$tmp"
  echo "check_sv_chain self-test: $ok ok, $bad failed"
  [ "$bad" = 0 ]
}

case "${1:-}" in
  "")          build_all; exit $? ;;
  --list)      [ "$#" = 1 ] || { echo "check_sv_chain: --list takes no further argument" >&2; exit 2; }
               collect; print_list; exit 0 ;;
  --dependents) [ "$#" -gt 1 ] || { echo "check_sv_chain: --dependents takes at least one path" >&2; exit 2; }
               shift; dependents "$@"; exit $? ;;
  --self-test) [ "$#" = 1 ] || { echo "check_sv_chain: --self-test takes no further argument" >&2; exit 2; }
               self_test; exit $? ;;
  *)           echo "check_sv_chain: unknown argument (got: $*)" >&2
               echo "  Accepted: no argument (build), --list, --dependents PATH..., --self-test." >&2
               exit 2 ;;
esac
