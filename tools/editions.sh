#!/usr/bin/env bash
# tools/editions.sh — §2.4's edition contract: thin siblings, and no
# definition parameterised by an edition.
#
# §2.4 is the most-cited home in the tree, and after `tools/laws.sh`'s
# attribution fix it is the head by breadth too: seven ungated laws.  This
# gates the two that a script can decide.
#
# STMT-60 — NO DEFINITION TAKES A VERSION PARAMETER.
#
# > CANNOT SEE A VERSION SMUGGLED AS A `Nat` OR A `String`.  A definition
# > taking `(v : Nat)` that means the edition is invisible to a type-based
# > rule, and that is the spelling someone reaching for the forbidden thing
# > would use.  THIS CATCHES THE HONEST SPELLING ONLY, and the report says so
# > every run rather than in a footnote.
#
# And it must not convict clause (4)'s legitimate case.  §2.4(4) records that
# for Go the edition is a property of the FILE, carried as data — so
# `perIterationLoopVars (v : LangVersion) : Bool` is a CLASSIFICATION over
# that data, not a semantics parameterised by edition.  The discriminator is
# the RETURN type: a definition returning a plain `Bool`/`String`/`Nat` is
# classifying metadata; one returning a semantic object (a monad, a state, a
# value) is the thing §2.4 forbids.
#
# STMT-59 — THIN SIBLINGS OVER A THICK SHARED TRUNK, reported as each
# sibling's size against its trunk beside the census convicting its files.
#
# USAGE
#   tools/editions.sh              # both checks
#   tools/editions.sh --self-test
#
# ZERO Lean execution.  Safe outside a tenure (A11).

set -u

CLONE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SELF_TEST=0

usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }
die()   { echo "editions.sh: $*" >&2; exit 2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --dir)       CLONE="${2:-}"; shift 2 ;;
    --self-test) SELF_TEST=1; shift ;;
    -h|--help)   usage ;;
    *)           die "unknown argument '$1'" ;;
  esac
done

lean_files() { find "$CLONE/LeanModels" -name '*.lean' -type f 2>/dev/null | LC_ALL=C sort; }

# A RETURN TYPE THAT CLASSIFIES rather than computes.  Kept as a named list so
# a lane can dispute the list instead of the verdict.
CLASSIFYING='Bool|String|Nat|Int|Option [A-Za-z]+|Prop'

# STMT-60.  Emits "file:line<TAB>verdict<TAB>decl<TAB>ret".
version_params() {
  local f
  for f in $(lean_files); do
    awk -v FN="${f#"$CLONE"/}" -v CLS="$CLASSIFYING" '
      function strip(line,   out, i, n, two) {
        out = ""; i = 1; n = length(line)
        while (i <= n) {
          two = substr(line, i, 2)
          if (depth == 0 && two == "--") break
          if (two == "/-") { depth++; i += 2; continue }
          if (two == "-/") { if (depth > 0) depth--; i += 2; continue }
          if (depth == 0) out = out substr(line, i, 1)
          i++
        }
        return out
      }
      { code = strip($0) }
      code ~ /^[ \t]*(private[ \t]+)?(partial[ \t]+)?(def|abbrev)[ \t]+/ {
        buf = code; startln = NR
        if (buf !~ /:=/ && buf !~ /:[ \t]*[A-Za-z]/) { collecting = 1; next }
        emit(); next
      }
      collecting { buf = buf " " code; if (buf ~ /:=/ || NR - startln > 4) { emit(); collecting = 0 } }
      function emit(   name, ret, verdict) {
        # A binder whose TYPE names a version or an edition.
        if (buf !~ /\([A-Za-z_][A-Za-z0-9_]*[ \t]*:[ \t]*[A-Za-z.]*([Vv]ersion|[Ee]dition)[A-Za-z]*[ \t]*\)/) return
        name = buf; sub(/^[ \t]*(private[ \t]+)?(partial[ \t]+)?(def|abbrev)[ \t]+/, "", name)
        sub(/[ \t(].*$/, "", name)
        ret = buf; sub(/:=.*$/, "", ret); sub(/^.*\)[ \t]*:[ \t]*/, "", ret)
        gsub(/^[ \t]+|[ \t]+$/, "", ret)
        verdict = (ret ~ ("^(" CLS ")$")) ? "clause-4" : "VIOLATION"
        printf "%s:%d\t%s\t%s\t%s\n", FN, startln, verdict, name, (ret == "" ? "?" : ret)
      }
      END { if (collecting) emit() }' "$f"
  done
}

# STMT-59 — THIN SIBLINGS OVER A THICK SHARED TRUNK.  The law states its own
# test: "if a sibling is thick, either the editions really do differ that much
# (measure and prove it) or the census was not run."
#
# > CANNOT SEE WHETHER THICKNESS IS JUSTIFIED.  It pairs the thickness with the
# > presence or absence of a conviction record and stops there.
#
# It also carries the THEOREM split, which is what STMT-61 (clause 2, theorems
# prove once on the trunk) actually needs in this tree: measured 2026-08-23,
# the C trunk holds ZERO theorems and its C23 sibling holds SEVEN, so a
# duplicate-statement finder would report nothing forever.  The failure mode
# here is not "proved twice" — it is "proved ONLY in the sibling", and that is
# a number a human can act on.
siblings() {                    # -> "lang<TAB>ver<TAB>sibLines<TAB>trunkLines<TAB>sibThms<TAB>trunkThms"
  local d lang ver sl tl st tt
  for d in $(find "$CLONE/LeanModels" -mindepth 2 -maxdepth 2 -type d 2>/dev/null | LC_ALL=C sort); do
    ver="$(basename "$d")"; lang="$(basename "$(dirname "$d")")"
    case "$ver" in
      C17|C23|[Pp]y3*|ES20*|[0-9]*|*[0-9][0-9]) ;;
      *) continue ;;
    esac
    sl="$(find "$d" -name '*.lean' -exec cat {} + 2>/dev/null | grep -c . || true)"
    tl="$(find "$CLONE/LeanModels/$lang" -maxdepth 1 -name '*.lean' -exec cat {} + 2>/dev/null | grep -c . || true)"
    st="$(find "$d" -name '*.lean' -exec grep -h '^theorem \|^lemma ' {} + 2>/dev/null | grep -c . || true)"
    tt="$(find "$CLONE/LeanModels/$lang" -maxdepth 1 -name '*.lean' -exec grep -h '^theorem \|^lemma ' {} + 2>/dev/null | grep -c . || true)"
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$lang" "$ver" "$sl" "$tl" "$st" "$tt"
  done
}

# §2.4(1) asks for a measurement convicting THE FILE.  A census that convicts
# CLAUSES is a real measurement and not that one, so the two are reported
# apart: saying "no census" when a clause delta exists would be as wrong as
# saying the file is convicted.
conviction_for() {              # lang, ver -> the conviction record, precisely
  local lang="$1" ver="$2" c
  for c in "$CLONE"/docs/*.json; do
    [ -f "$c" ] || continue
    if grep -qE "LeanModels/$lang/$ver/[A-Za-z0-9_]*\.lean" "$c" 2>/dev/null; then
      printf 'FILES: %s\n' "$(basename "$c")"; return 0
    fi
  done
  # A census whose NAME belongs to this tier first: the first version took the
  # alphabetically-first JSON containing the token and credited C23's
  # conviction to `ada-suite-census.json`, which matched a test name.  A
  # coincidental token is not a conviction record.
  local lc; lc="$(printf '%s' "$lang" | tr 'A-Z' 'a-z')"
  local vc; vc="$(printf '%s' "$ver" | tr 'A-Z' 'a-z')"
  # Anchored: `docs/c-*.json` and `docs/*c23*.json`, not `*c*` — which matched
  # the word "census" in every filename in the directory.
  for c in "$CLONE"/docs/"$lc"-*.json "$CLONE"/docs/*"$vc"-*.json "$CLONE"/docs/*-"$vc"-*.json; do
    [ -f "$c" ] || continue
    if grep -qiE "\"?$ver\"?" "$c" 2>/dev/null; then
      printf 'clauses only: %s (no census names the FILES)\n' "$(basename "$c")"; return 0
    fi
  done
  printf 'NO MEASUREMENT AT ALL\n'
}

# --------------------------------------------------------------- self-test
if [ "$SELF_TEST" = "1" ]; then
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/editions-selftest.XXXXXX")" || die "no temp dir"
  trap 'rm -rf "$tmp"' EXIT
  ok=0; bad=0
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; \
            else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }

  fx="$tmp/fx"; mkdir -p "$fx/LeanModels/T"
  cat > "$fx/LeanModels/T/A.lean" <<'LEAN'
def perIterationLoopVars (v : LangVersion) : Bool :=
  v.minor >= 22
def evalExpr (v : LangVersion) (e : Expr) : SemM Val :=
  go e
def innocent (e : Expr) : SemM Val :=
  go e
/-- A doc comment mentioning (v : LangVersion) : SemM Val -/
def documented (e : Expr) : Nat := 0
def edited (ed : Edition) (s : Stmt) : Flow :=
  step s
LEAN
  CLONE="$fx"

  check "a version-typed binder is found"     "$(version_params | grep -c .)" "3"
  check "  ...a Bool return is clause-4"      "$(version_params | awk -F'\t' '$3=="perIterationLoopVars"{print $2}')" "clause-4"
  check "  ...a semantic return is a VIOLATION" "$(version_params | awk -F'\t' '$3=="evalExpr"{print $2}')" "VIOLATION"
  check "  ...and it names the return type"   "$(version_params | awk -F'\t' '$3=="evalExpr"{print $4}')" "SemM Val"
  check "an Edition binder counts too"        "$(version_params | awk -F'\t' '$3=="edited"{print $2}')" "VIOLATION"
  check "a def with no version binder is silent" "$(version_params | grep -c innocent)" "0"
  check "prose about one is not one"          "$(version_params | grep -c documented)" "0"

  # ---- STMT-59 + the theorem split STMT-61 needs
  mkdir -p "$fx/LeanModels/L/V23" "$fx/docs"
  printf 'theorem a : True := trivial\ndef x := 1\n' > "$fx/LeanModels/L/V23/S.lean"
  printf 'def y := 2\ndef z := 3\ndef w := 4\n' > "$fx/LeanModels/L/T.lean"
  set -- $(siblings | grep '^L	')
  check "a sibling is found under its trunk"  "$2" "V23"
  check "  ...with its own line count"        "$3" "2"
  check "  ...and the trunk's"                "$4" "3"
  check "  ...and the THEOREM split"          "$5:$6" "1:0"
  check "a non-edition dir is not a sibling"  "$(siblings | grep -c '	T	')" "0"

  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

# -------------------------------------------------------------------- main
[ -d "$CLONE/LeanModels" ] || die "no LeanModels/ under '$CLONE'"

echo "editions.sh — §2.4's edition contract"
echo "              measured at $(git -C "$CLONE" rev-parse --short HEAD 2>/dev/null || echo 'no git')"
echo
echo "  STMT-60 — no definition takes a version parameter."
echo "  CATCHES THE HONEST SPELLING ONLY: a version smuggled as a \`Nat\` or a"
echo "  \`String\` is invisible to a type-based rule, and that is the spelling"
echo "  someone reaching for the forbidden thing would use."
echo
ROWS="$(version_params)"
NV="$(printf '%s' "$ROWS" | awk -F'\t' '$2=="VIOLATION"' | grep -c . || true)"
NC="$(printf '%s' "$ROWS" | awk -F'\t' '$2=="clause-4"' | grep -c . || true)"
printf '  VIOLATIONS  %s        clause-4 CLASSIFIERS (allowed)  %s\n' "$NV" "$NC"
if [ -n "$ROWS" ]; then
  echo
  printf '%s\n' "$ROWS" | awk -F'\t' '{ printf "    %-9s %-42s %-22s -> %s\n", $2, $1, $3, $4 }'
fi
echo
echo
echo "  STMT-59 — thin siblings over a thick shared trunk."
echo "  CANNOT SEE WHETHER THICKNESS IS JUSTIFIED: it pairs thickness with the"
echo "  presence of a conviction record and stops there."
echo
printf '  %-6s %-6s %8s %8s %6s  %-8s %s\n' LANG VER SIBLING TRUNK RATIO THEOREMS CONVICTED-BY
SIBS="$(siblings)"
if [ -z "$SIBS" ]; then
  echo "    (no edition siblings in the tree — one row appears when a lane forks)"
else
  printf '%s\n' "$SIBS" | while IFS="$(printf '\t')" read -r lang ver sl tl st tt; do
    ratio="$(awk -v a="$sl" -v b="$tl" 'BEGIN { if (b+0 == 0) print "n/a"; else printf "%.2f", a/b }')"
    printf '  %-6s %-6s %8s %8s %6s  %3s/%-4s %s\n' "$lang" "$ver" "$sl" "$tl" "$ratio" \
      "$st" "$tt" "$(conviction_for "$lang" "$ver")"
  done
fi
echo
echo "  THEOREMS is sibling/trunk. §2.4(2) says theorems prove ONCE on the"
echo "  TRUNK, so a sibling holding theorems the trunk does not is the shape to"
echo "  look at — measured here rather than inferred, because in this tree the"
echo "  failure is not 'proved twice' but 'proved only in the sibling'."
echo
echo "  clause-4 is §2.4(4)'s legitimate case: for Go the edition is a property"
echo "  of the FILE, carried as data, so a predicate CLASSIFYING that data is"
echo "  not a semantics parameterised by edition. The discriminator is the"
echo "  RETURN type — dispute the list ($CLASSIFYING), not the verdict."
