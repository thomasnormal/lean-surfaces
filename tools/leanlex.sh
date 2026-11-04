# tools/leanlex.sh — the Lean lexing primitives, ONCE.
#
# Sourced, not executed.  Four tools had grown their own copy of the same
# comment walker (`sites.sh`, `triad.sh`, and `substrate.sh` needed a third and
# fourth), which is precisely what `tools/dupes.sh` counts and MEAS-28
# forbids.  The 2026-08-23 audit found three separate defects that all reduce
# to "this matcher does not know what a comment is", so the primitive moves
# here and the copies retire BY TOUCH (§9.2).
#
#   lean_code_lines <file>    -> "lineno:code" per line, comments removed
#   lean_decl_blocks <file>   -> "lineno:decl-text" per declaration, comments
#                                removed and continuation lines joined
#
# Lean block comments NEST, so depth is tracked rather than paired.  The known
# approximation is `--` inside a string literal; it errs toward removing text,
# which is stated at each call site that cares.

lean_code_lines() {             # file -> "lineno:code" for non-blank code
  awk '
    {
      line = $0; out = ""; i = 1; n = length(line)
      while (i <= n) {
        two = substr(line, i, 2)
        if (depth == 0 && two == "--") break
        if (two == "/-") { depth++; i += 2; continue }
        if (two == "-/") { if (depth > 0) depth--; i += 2; continue }
        if (depth == 0) out = out substr(line, i, 1)
        i++
      }
      if (out ~ /[^ \t]/) printf "%d:%s\n", NR, out
    }' "$1"
}

# One DECLARATION per record, so a matcher can ask "do both names appear in the
# SAME statement?" — the question two independent greps over a file cannot
# answer, and the defect the audit found in `adequacy_for`.
lean_decl_blocks() {            # file -> "lineno:joined declaration text"
  awk '
    function flush() {
      if (start > 0 && buf ~ /[^ \t]/) printf "%d:%s\n", start, buf
      start = 0; buf = ""
    }
    {
      line = $0; out = ""; i = 1; n = length(line)
      while (i <= n) {
        two = substr(line, i, 2)
        if (depth == 0 && two == "--") break
        if (two == "/-") { depth++; i += 2; continue }
        if (two == "-/") { if (depth > 0) depth--; i += 2; continue }
        if (depth == 0) out = out substr(line, i, 1)
        i++
      }
      if (out ~ /^[ \t]*(@\[|private |protected |partial |noncomputable |theorem |lemma |def |abbrev |instance |structure |inductive |example |class |opaque )/) {
        flush(); start = NR; buf = out; next
      }
      if (start > 0) buf = buf " " out
    }
    END { flush() }' "$1"
}

# A NAME, matched as a whole name.  `$a` raw satisfies a grep from any longer
# identifier that contains it, which is how one line satisfied two independent
# checks in `adequacy_for`.
lean_names_both() {             # text, nameA, nameB -> 0 when BOTH appear whole
  printf '%s' "$1" | grep -qE "(^|[^A-Za-z0-9_'])$2([^A-Za-z0-9_']|$)" || return 1
  printf '%s' "$1" | grep -qE "(^|[^A-Za-z0-9_'])$3([^A-Za-z0-9_']|$)" || return 1
  return 0
}
