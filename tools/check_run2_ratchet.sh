#!/usr/bin/env bash
# tools/check_run2_ratchet.sh — no NEW work on the retiring run layer: a ratchet against a committed baseline.
#
# WHY.  The SystemVerilog tier has two meanings: E (`LeanModels/Sv/Kernel`, the authority) and the fueled interpreter
# `run2` with its cycle model and judgments. Decided 2026-11-09: `run2` retires and E becomes the only meaning
# (docs/sv-kernel.md, "Debts", row "run2 retirement"). The `Stmt2` freeze held at the type level and the drift went around
# it: new views, admissions and statements kept landing on the run route. A convention did not stop that, so this is a
# check that fails.
#
# WHAT IT COUNTS.  Mentions of the run layer's names in Lean CODE:
#     run2  runFrom2  cycleStep2  combSettle2  execStmt2  evalExpr2  Runs2  Terminates2  and the judgment sign `⊨₂`
#   * SCOPE: every `*.lean` file in the checkout. Any file that imports the Sv tier can name the layer, so this is not a
#     directory list. A `.lake` directory is skipped at any depth, and so is a top-level `svgolf/` (it is not on master;
#     its own plan moves it). Not read either: a top-level directory whose name starts with `.`, and a `.lean` that is a
#     symlink below the top level (on 2026-11-10 the tree tracks neither kind).
#   * COMMENTS DO NOT COUNT: line comments, block comments and docstrings are removed first by `lean_code_lines`
#     (tools/leanlex.sh, the tree's one Lean lexer). A label such as "provisional over run2" in a docstring is free.
#   * WORD MATCHING. A name counts as a whole word, where the words of an identifier are separated by `_`, `.` and a
#     camel-case hump: it must not be followed by a lowercase letter or digit; a name that starts in lower case must not
#     follow a letter or digit, and one that starts in upper case (`Runs2`, `Terminates2`) must not follow an upper-case
#     letter. So `Sv.run2`, `run2_mono`, `Obs_run2`, `run2ClockGuard`, `closed_eq_combSettle2` and `run2'` count (each is
#     run-layer: every such identifier on master was read, 2026-11-09), so would a new `seqRuns2`, and `overrun2`,
#     `run2x`, `run20` and `ERuns2` do not. The sign `⊨₂` counts wherever it stands. Matching is case-sensitive.
#   * The unit is the MENTION, not the line: a second name added to a line that already has one is growth.
#
# THE RATCHET.  The baseline (`tools/run2_ratchet.baseline`) lists the files that name the layer, with their counts.
#   1. A file that names the layer and is not in the baseline FAILS.
#   2. A total above the baseline's total FAILS.
#   Everything else passes: moving code between two baseline files, and every removal. The per-file counts in the
#   baseline are there to say where growth happened; only the file set and the total decide.
#
# WHAT IT DOES NOT CATCH (it under-reports, and says so).
#   * Run-layer work that uses none of the names above: the derived runners and views (`runObs2`, `cycleObs2`,
#     `runMem2`, `runHier2`, `runCombProcess2`, ...) are not in the list. On 2026-11-09, 19 files name one of those and
#     none of the listed names. Nor is the capitalised `Run2` of `toRun2`, `ofRun2`, `REdgeRun2` and `FlatMemRun2`.
#   * Growth that a removal pays for: new work in one baseline file, with as many mentions removed elsewhere, passes.
#     A baseline left above the tree (after removals, before `--regenerate`) leaves that much room.
#   * Work outside Lean: an extractor rewrite into the run layer's vocabulary is invisible here.
#   * Lexer limits (tools/leanlex.sh does not know string literals). `--` inside a string reads as a line comment, so
#     the rest of that line is not counted. `/-` inside a string reads as a block comment that never closes, which
#     would hide the rest of the file (`LeanModels/Sv/Param.lean` from line 2762, measured 2026-11-09); the gate
#     detects that with a marker line appended after the file and then counts the WHOLE file, comments included, so
#     such a file over-counts rather than hides. It does NOT detect the case where a later `-/` (in another string, or
#     in a comment) closes that false comment: the code between the two is hidden, and the marker still arrives. On
#     2026-11-10 neither limit hides a mention (an independent string-aware count agreed with this gate file by file). A
#     name inside a string literal on a code line DOES count.
#
# REGENERATING.  For a module split, a file move, or work that was in flight on 2026-11-09:
#     bash tools/check_run2_ratchet.sh --regenerate
#   rewrites the baseline from the tree and prints what changed. Commit it with the change that needed it and say why:
#   the baseline's diff is where a reviewer sees the layer grow. After a removal the same command locks the gain in.
#
# USAGE      bash tools/check_run2_ratchet.sh               compare the tree with the baseline
#            bash tools/check_run2_ratchet.sh --count       print `<count> <path> <first lines>` and the total; no comparison
#            bash tools/check_run2_ratchet.sh --regenerate  rewrite the baseline from the tree
#            bash tools/check_run2_ratchet.sh --self-test   the logic over fixture trees, and the gate on this tree
# EXIT       0 pass; 1 the ratchet failed; 2 usage error, or the tree or the baseline could not be read.
# Runs no Lean. A few seconds.
set -u
cd "$(dirname "$0")/.."

BASELINE=tools/run2_ratchet.baseline
TOKENS='run2 runFrom2 cycleStep2 combSettle2 execStmt2 evalExpr2 Runs2 Terminates2 ⊨₂'
REGEN='bash tools/check_run2_ratchet.sh --regenerate'
MARK='RATCHET_END_OF_FILE_MARK'      # appended after each file: if the lexer does not return it, it lost the file's tail
TAB="$(printf '\t')"

[ -r tools/leanlex.sh ] || { echo "check_run2_ratchet: tools/leanlex.sh is missing (the Lean lexer this gate uses)" >&2; exit 2; }
. tools/leanlex.sh

# ---------------------------------------------------------------- the tree
# Every Lean source, as a root-relative path. The top-level entries are walked one by one with `find -H`, because
# `tools/ci.sh` runs self-tests in a view where each of them is a symlink.
scan_files() {
  local e
  for e in *; do
    case "$e" in svgolf) continue ;; esac
    if [ -d "$e" ]; then
      find -H "$e" -name .lake -prune -o -type f -name '*.lean' -print 2>/dev/null
    else
      case "$e" in *.lean) [ -f "$e" ] && printf '%s\n' "$e" ;; esac
    fi
  done | LC_ALL=C sort -u
}

# stdin: `lineno:text` lines, ending with the marker line. stdout: `<mentions><TAB><the first five line numbers>`,
# or nothing when the marker did not arrive.
count_tokens() {
  LC_ALL=C awk -v toks="$TOKENS" -v mark="$MARK" '
    BEGIN { n = split(toks, T, " ") }
    {
      colon = index($0, ":"); s = substr($0, colon + 1); hit = 0
      if (s == mark) { seen = 1; next }
      for (k = 1; k <= n; k++) {
        t = T[k]; L = length(t); word = (t ~ /^[A-Za-z]/); up = (t ~ /^[A-Z]/); off = 0; rest = s
        while ((i = index(rest, t)) > 0) {
          at = off + i
          p = (at > 1) ? substr(s, at - 1, 1) : ""
          q = substr(s, at + L, 1)
          left = up ? (p !~ /[A-Z]/) : (p !~ /[A-Za-z0-9]/)
          if (!word || (left && q !~ /[a-z0-9]/)) { c++; hit = 1 }
          off = at + L - 1; rest = substr(s, off + 1)
        }
      }
      if (hit && shown < 5) { lines = lines (shown ? "," : "") substr($0, 1, colon - 1); shown++ }
    }
    END { if (seen) printf "%d\t%s\n", c, lines }'
}

# One file: its code through the tree's lexer; the whole text when the lexer ends inside a comment it never closes.
count_file() {
  local r
  r="$({ cat "$1"; printf '\n%s\n' "$MARK"; } | lean_code_lines - | count_tokens)"
  if [ -z "$r" ]; then
    r="$({ cat "$1"; printf '\n%s\n' "$MARK"; } | grep -n '' | count_tokens)"
    r="$r (the whole file is counted, comments too: the lexer loses its code at a comment opener inside a string)"
  fi
  printf '%s\n' "$r"
}

# `<mentions><TAB><path><TAB><lines>` for every file whose code names the layer, in path order. The fixed-string grep
# is only a prefilter (about one file in ten survives it); the count is made on the comment-free text.
counts() {
  local files f r args=() t
  files="$(scan_files)"
  [ -n "$files" ] || return 2
  for t in $TOKENS; do args+=(-e "$t"); done
  printf '%s\n' "$files" | tr '\n' '\0' | LC_ALL=C xargs -0 grep -lF "${args[@]}" /dev/null 2>/dev/null | LC_ALL=C sort -u |
    while IFS= read -r f; do
      r="$(count_file "$f")"
      [ "${r%%"$TAB"*}" -gt 0 ] && printf '%s\t%s\t%s\n' "${r%%"$TAB"*}" "$f" "${r#*"$TAB"}"
    done
  return 0
}

total_of() { awk -F'\t' '{ s += $1 } END { print s + 0 }'; }
paths_of() { cut -f2; }
nonblank() { grep -c . || true; }

# The baseline's data lines: `<mentions><TAB><path>`.
read_baseline() { grep -v '^#' "$BASELINE" | grep . || true; }

baseline_ok() {
  [ -r "$BASELINE" ] || { echo "check_run2_ratchet: no baseline at $BASELINE (write one with: $REGEN)" >&2; return 2; }
  if read_baseline | grep -qvE "^[0-9]+$TAB[^$TAB]+\$"; then
    echo "check_run2_ratchet: $BASELINE has a line that is not '<count><TAB><path>' (rewrite it with: $REGEN)" >&2
    return 2
  fi
  return 0
}

# ---------------------------------------------------------------- the comparison
explain() {
  cat >&2 <<EOF
=== [run2-ratchet] FAILED
    run2 is being retired: docs/sv-kernel.md, "Debts", row "run2 retirement" (decided 2026-11-09).
    No new work is built on the run layer. New constructs, views, statements and tactics go on E
    (LeanModels/Sv/Kernel); text in a comment or a docstring is not counted.
    If this change is a module split, a file move, or work that was in flight on 2026-11-09, regenerate the
    baseline, commit it with the change, and say why in the commit message:
        $REGEN
EOF
}

check_tree() {
  local cur base tc tb fc fb new grown bad=0
  baseline_ok || return 2
  cur="$(counts)" || { echo "check_run2_ratchet: found no Lean files (run it from a checkout)" >&2; return 2; }
  base="$(read_baseline)"
  tc="$(printf '%s\n' "$cur" | total_of)"; tb="$(printf '%s\n' "$base" | total_of)"
  fc="$(printf '%s\n' "$cur" | nonblank)"; fb="$(printf '%s\n' "$base" | nonblank)"
  # rule 1: a file that names the layer and is not in the baseline
  new="$(printf '%s\n' "$cur" | awk -F'\t' '
    NR == FNR { if ($2 != "") seen[$2] = 1; next }
    $2 != "" && !($2 in seen) { printf "    %s: %d (at lines %s)\n", $2, $1, $3 }' <(printf '%s\n' "$base") -)"
  if [ -n "$new" ]; then
    bad=1
    echo "=== [run2-ratchet] these files name the run layer and are not in the baseline (mentions; the first five lines):" >&2
    printf '%s\n' "$new" >&2
  fi
  # rule 2: the total
  if [ "$tc" -gt "$tb" ]; then
    bad=1
    echo "=== [run2-ratchet] the run layer grew: $tc mentions, the baseline has $tb (+$((tc - tb)))" >&2
    grown="$(printf '%s\n' "$cur" | awk -F'\t' '
      NR == FNR { if ($2 != "") was[$2] = $1; next }
      ($2 in was) && $1 + 0 > was[$2] + 0 { printf "    %s: %d -> %d\n", $2, was[$2], $1 }' <(printf '%s\n' "$base") -)"
    [ -n "$grown" ] && { echo "    files above their baseline count:" >&2; printf '%s\n' "$grown" >&2; }
  fi
  if [ "$bad" = 1 ]; then explain; return 1; fi
  echo "=== [run2-ratchet] OK: $tc mentions of the run layer in $fc files (baseline: $tb in $fb)"
  [ "$tc" -lt "$tb" ] && echo "    $((tb - tc)) below the baseline. Lock it in: $REGEN"
  return 0
}

print_counts() {
  local cur
  cur="$(counts)" || { echo "check_run2_ratchet: found no Lean files (run it from a checkout)" >&2; return 2; }
  [ -n "$cur" ] && printf '%s\n' "$cur"
  echo "total: $(printf '%s\n' "$cur" | total_of) mentions in $(printf '%s\n' "$cur" | nonblank) files"
}

regenerate() {
  local cur old="" tb="none" tc
  cur="$(counts)" || { echo "check_run2_ratchet: found no Lean files (run it from a checkout)" >&2; return 2; }
  if [ -r "$BASELINE" ]; then old="$(read_baseline)"; tb="$(printf '%s\n' "$old" | total_of)"; fi
  {
    echo "# tools/run2_ratchet.baseline: the files whose Lean code names the retiring run layer, with the number of mentions."
    echo "# Written by \`$REGEN\`; do not edit by hand. Read by tools/check_run2_ratchet.sh, which"
    echo "# fails on a file that is not listed here and on a total above this file's total. Why: docs/sv-kernel.md, \"Debts\","
    echo "# row \"run2 retirement\". Format: <mentions><TAB><path>, in C-locale path order."
    [ -n "$cur" ] && printf '%s\n' "$cur" | cut -f1,2
  } > "$BASELINE" || { echo "check_run2_ratchet: could not write $BASELINE" >&2; return 2; }
  tc="$(printf '%s\n' "$cur" | total_of)"
  echo "=== [run2-ratchet] baseline rewritten: $tb -> $tc mentions, $(printf '%s\n' "$cur" | nonblank) files"
  diff <(printf '%s\n' "$old" | paths_of | grep .) <(printf '%s\n' "$cur" | paths_of | grep .) |
    sed -n -e 's/^< /    no longer listed: /p' -e 's/^> /    newly listed:     /p'
  return 0
}

# ---------------------------------------------------------------- the self-test: fixture trees, no Lean
self_test() {
  local tmp ok=0 bad=0 rc out self="$PWD/tools/check_run2_ratchet.sh" lex="$PWD/tools/leanlex.sh"
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/run2-ratchet-st.XXXXXX")" || return 2
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }
  local tree="$tmp/tree"
  mk() { mkdir -p "$(dirname "$tree/$1")"; printf '%s\n' "$2" > "$tree/$1"; }
  gate() { out="$(cd / && bash "$tree/tools/check_run2_ratchet.sh" "$@" 2>&1)"; rc=$?; }
  mkdir -p "$tree/tools"; cp "$self" "$lex" "$tree/tools/"
  mk LeanModels/Sv/A.lean       'theorem a : run2 d = run2 d := rfl'
  mk LeanModels/Sv/B.lean       'def b := cycleStep2 d'
  mk LeanModels/Sv/Clean.lean   'def c := 1'
  mk Root.lean                  'def r := combSettle2'

  gate
  check "no baseline is not a pass" "$rc" 2
  check "  ...and the message gives the regenerate command" "$(printf '%s' "$out" | grep -c -- '--regenerate')" 1
  gate --regenerate
  check "--regenerate exits 0" "$rc" 0
  check "the baseline lists counts by path" "$(grep -v '^#' "$tree/tools/run2_ratchet.baseline" | tr '\t\n' ' ;')" "2 LeanModels/Sv/A.lean;1 LeanModels/Sv/B.lean;1 Root.lean;"
  cp "$tree/tools/run2_ratchet.baseline" "$tmp/base0"
  gate --regenerate
  check "--regenerate on an unchanged tree writes the same file" "$(cmp -s "$tmp/base0" "$tree/tools/run2_ratchet.baseline" && echo same)" same
  gate
  check "the clean tree passes" "$rc" 0
  check "  ...and reports the total" "$(printf '%s' "$out" | grep -c 'OK: 4 mentions of the run layer in 3 files')" 1

  # rule 2: growth inside a baseline file
  printf '%s\n' 'def a2 := run2 d' >> "$tree/LeanModels/Sv/A.lean"; gate
  check "a code line naming run2 in a baseline file fails" "$rc" 1
  check "  ...naming the file and its counts" "$(printf '%s' "$out" | grep -c 'LeanModels/Sv/A.lean: 2 -> 3')" 1
  check "  ...the debt row" "$(printf '%s' "$out" | grep -c 'row "run2 retirement"')" 1
  check "  ...that new work goes on E" "$(printf '%s' "$out" | grep -c 'go on E')" 1
  check "  ...and the regenerate command" "$(printf '%s' "$out" | grep -c 'bash tools/check_run2_ratchet.sh --regenerate')" 1
  mk LeanModels/Sv/A.lean 'theorem a : run2 d = run2 d ∧ Runs2 d := rfl'; gate
  check "a second name on an existing line is growth" "$rc" 1
  mk LeanModels/Sv/A.lean 'theorem a : run2 d = run2 d := rfl'

  # rule 1: a new file
  mk Examples/new/N.lean 'def n := Terminates2 d'; gate
  check "a new file naming the layer fails" "$rc" 1
  check "  ...naming it and the line" "$(printf '%s' "$out" | grep -c 'Examples/new/N.lean: 1 (at lines 1)')" 1
  printf '%s\n' 'def b := 0' > "$tree/LeanModels/Sv/B.lean"; gate
  check "  ...even when the total does not grow" "$rc" 1
  mk LeanModels/Sv/B.lean 'def b := cycleStep2 d'
  rm -rf "$tree/Examples/new"
  mk Extra.lean 'def e := d ⊨₂ p'; gate
  check "a new top-level file naming the sign fails" "$rc" 1
  rm -f "$tree/Extra.lean"

  # comments and docstrings are free
  mk LeanModels/Sv/Clean.lean '/-- Provisional over run2: the cycle model `cycleStep2`. -/
def c := 1  -- run2 again
/- a block comment: /- nested run2 -/ still inside, Runs2 -/
/-! a module docstring about combSettle2 -/'
  gate
  check "a docstring, a line comment and a nested block comment do not count" "$rc" 0
  printf '%s\n' '/-- Provisional over run2. -/' >> "$tree/LeanModels/Sv/A.lean"; gate
  check "a docstring in a baseline file does not count" "$rc" 0
  mk LeanModels/Sv/Clean.lean '/- closed -/ def c := run2'; gate
  check "code after a closed comment on the same line counts" "$rc" 1
  mk LeanModels/Sv/Clean.lean 'def c := 1'
  mk LeanModels/Sv/A.lean 'theorem a : run2 d = run2 d := rfl'
  # a comment opener inside a string: the lexer would lose the rest of the file, so the whole file is counted
  mk LeanModels/Sv/Str.lean 'def s := "the ++/-- tier"
def t := run2 d'
  gate
  check "code below a comment opener inside a string is still seen" "$rc" 1
  check "  ...and the report says the whole file is counted" "$(printf '%s' "$out" | grep -c 'LeanModels/Sv/Str.lean: 1 (at lines 2 (the whole file is counted')" 1
  mk LeanModels/Sv/Str.lean 'def s := "the ++/-- tier"
def t := 1'
  gate
  check "  ...a file like that with no mention passes" "$rc" 0
  rm -f "$tree/LeanModels/Sv/Str.lean"

  # moving between baseline files, and removal
  mk LeanModels/Sv/A.lean 'theorem a : True := trivial'
  mk LeanModels/Sv/B.lean 'def b := cycleStep2 d
theorem a : run2 d = run2 d := rfl'
  gate
  check "moving a line between two baseline files passes" "$rc" 0
  mk LeanModels/Sv/B.lean 'def b := cycleStep2 d'; gate
  check "a removal passes" "$rc" 0
  check "  ...and says how to lock it in" "$(printf '%s' "$out" | grep -c '2 below the baseline')" 1
  mk LeanModels/Sv/A.lean 'theorem a : run2 d = run2 d := rfl'

  # the regenerate command restores a pass
  mk Examples/new/N.lean 'def n := Terminates2 d'; gate
  check "before --regenerate: the new file fails" "$rc" 1
  gate --regenerate
  check "--regenerate names the new file" "$(printf '%s' "$out" | grep -c 'newly listed:     Examples/new/N.lean')" 1
  gate
  check "after --regenerate: the gate passes" "$rc" 0
  rm -rf "$tree/Examples/new"; gate --regenerate
  check "--regenerate names a file that left" "$(printf '%s' "$out" | grep -c 'no longer listed: Examples/new/N.lean')" 1

  # word matching
  word() { mk LeanModels/Sv/W.lean "$1"; gate --count; out="$(printf '%s\n' "$out" | awk -F'\t' '$2 == "LeanModels/Sv/W.lean" { print $1 }')"; }
  word 'def w := Sv.run2 d'                  ; check "word: a namespaced name counts" "$out" 1
  word 'theorem run2_mono : True := trivial' ; check "word: a lemma name with _ counts" "$out" 1
  word 'def w := Obs_run2 d'                 ; check "word: a name after _ counts" "$out" 1
  word 'def w := run2ClockGuard d'           ; check "word: a name before a camel-case hump counts" "$out" 1
  word "def w := run2' d"                    ; check "word: a primed name counts" "$out" 1
  word 'def w := (run2 d, run2 d)'           ; check "word: two mentions on a line count twice" "$out" 2
  word 'def w := closed_eq_combSettle2_lower'; check "word: a name between two _ counts" "$out" 1
  word 'def w := d ⊨₂ p'                     ; check "word: the judgment sign counts" "$out" 1
  word 'def w := overrun2 d'                 ; check "word: a name inside a longer word does not count" "$out" ""
  word 'def w := run2x + run20'              ; check "word: a name followed by a lowercase letter or digit does not count" "$out" ""
  word 'def w := ERuns2 d'                   ; check "word: a name after a capital does not count" "$out" ""
  word 'def w := seqRuns2 d ∧ x2Terminates2 d'; check "word: a camel-case hump before a capitalised name counts" "$out" 2
  word 'def w := xrun2 d ∧ XcycleStep2 d'    ; check "word: a lower-case name after any letter does not count" "$out" ""
  word 'def w := Run2 d + runObs2 d'         ; check "word: matching is case-sensitive, and runObs2 is not in the list" "$out" ""
  word 'def w := "run2: timeout"'            ; check "word: a name in a string literal counts" "$out" 1
  rm -f "$tree/LeanModels/Sv/W.lean"

  # scope
  mk svgolf/S.lean 'def s := run2'; mk LeanModels/.lake/P.lean 'def p := run2'; mk notes/n.txt 'run2'; gate
  check "svgolf/, a .lake directory and non-Lean files are not scanned" "$rc" 0
  mk harness/sv/R.lean 'def r := run2'; gate
  check "a Lean file under any other directory is scanned" "$rc" 1
  rm -rf "$tree/harness" "$tree/svgolf" "$tree/LeanModels/.lake" "$tree/notes"
  # the shape of tools/ci.sh's self-test view: the top-level entries are symlinks
  local linked="$tmp/linked" e; mkdir -p "$linked"
  for e in "$tree"/*; do ln -s "$e" "$linked/${e##*/}"; done
  out="$(cd "$linked" && bash tools/check_run2_ratchet.sh --count 2>&1 | tail -1)"
  check "a tree whose top-level entries are symlinks is read" "$out" "total: 4 mentions in 3 files"

  # refusals
  printf 'garbage line\n' >> "$tree/tools/run2_ratchet.baseline"; gate
  check "a malformed baseline is an error, not a pass" "$rc" 2
  local empty="$tmp/empty"; mkdir -p "$empty/tools"; cp "$self" "$lex" "$empty/tools/"; : > "$empty/tools/run2_ratchet.baseline"
  out="$(bash "$empty/tools/check_run2_ratchet.sh" 2>&1)"; rc=$?
  check "a tree with no Lean files is an error, not a pass" "$rc" 2
  out="$(bash "$self" --bogus 2>&1)"; rc=$?
  check "an unknown argument exits 2" "$rc" 2

  # this tree
  out="$(bash "$self" 2>&1)"; rc=$?
  check "this tree: the gate passes" "$rc" 0
  [ "$rc" = 0 ] || printf '%s\n' "$out"
  rm -rf "$tmp"
  echo "check_run2_ratchet self-test: $ok ok, $bad failed"
  [ "$bad" = 0 ]
}

case "${1:-}" in
  "")           check_tree; exit $? ;;
  --count)      [ "$#" = 1 ] || { echo "check_run2_ratchet: --count takes no further argument" >&2; exit 2; }
                print_counts; exit $? ;;
  --regenerate) [ "$#" = 1 ] || { echo "check_run2_ratchet: --regenerate takes no further argument" >&2; exit 2; }
                regenerate; exit $? ;;
  --self-test)  [ "$#" = 1 ] || { echo "check_run2_ratchet: --self-test takes no further argument" >&2; exit 2; }
                self_test; exit $? ;;
  *)            echo "check_run2_ratchet: unknown argument (got: $*)" >&2
                echo "  Accepted: no argument (check), --count, --regenerate, --self-test." >&2
                exit 2 ;;
esac
