#!/usr/bin/env bash
# tools/backlog-index.sh — GENERATE docs/backlog/INDEX.md from the per-lane
# files, because §9.5 says the index is generated and never hand-maintained.
#
# §9.5's own words: "`docs/backlog.md` becomes a GENERATED index, which is
# §5.5's 'generated and checked, never hand-maintained' applied to the
# repository's own record."  This is that generator.
#
# The monolith it replaces collided with itself — `L2`, `L3` and `L4` each
# appear TWICE — because every lane appended to one tail at ~66 landings a
# day.  Per-lane files remove the collision; an index puts the single view
# back without putting the contention back.
#
# USAGE
#   tools/backlog-index.sh              # write docs/backlog/INDEX.md
#   tools/backlog-index.sh --stdout     # print it, write nothing
#   tools/backlog-index.sh --check      # regenerate and DIFF: exit 1 on drift
#   tools/backlog-index.sh --install-merge-driver   # see below
#   tools/backlog-index.sh --ensure-driver          # idempotent; used by gates
#   tools/backlog-index.sh --self-test
#
# THE MERGE DRIVER.  Merging a generated file is always wrong: a merged index
# is a THIRD version matching neither tree.  `.gitattributes` marks this file
# `merge=ours` so a rebase resolves without a conflict — but `ours` is NOT a
# built-in driver (git ships `text`, `binary`, `union`), so each clone must
# also define it, or git falls back to a normal conflict.  Measured both ways.
# `--install-merge-driver` sets `merge.ours.driver=true` in THIS clone.
#
# EXIT  0 in sync (or written)   1 drift (--check)   2 refusal
#
# ZERO Lean execution.  Safe outside a tenure (A11).

set -u

CLONE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DIR=""
MODE="write"

usage() { sed -n '1,/^set -u/p' "${BASH_SOURCE[0]}" >&2; exit 2; }
die()   { echo "backlog-index.sh: $*" >&2; exit 2; }

. "$(dirname "${BASH_SOURCE[0]}")/argv.sh"   # the value-flag guard (a flag written last used to SPIN)
while [ $# -gt 0 ]; do
  case "$1" in
    --dir)       need_val "$#" "$1"; CLONE="$2"; shift 2 ;;
    --backlog)   need_val "$#" "$1"; DIR="$2"; shift 2 ;;
    --stdout)    MODE="stdout"; shift ;;
    --check)     MODE="check"; shift ;;
    --install-merge-driver) MODE="install-driver"; shift ;;
    --ensure-driver)        MODE="ensure-driver"; shift ;;
    --self-test) MODE="self-test"; shift ;;
    -h|--help)   usage ;;
    *)           die "unknown argument '$1'" ;;
  esac
done
[ -n "$DIR" ] || DIR="$CLONE/docs/backlog"

# One row per `## ` heading.  The id is the first token; everything after the
# first em dash is the title.  A heading that is not a dated id is REPORTED,
# not skipped — §9.5's scheme is `YYYY-MM-DD-<lane>-<n>`, and a drifter that
# is quietly dropped is a row nobody sees is missing.
# THE DRIVER NAME COMES FROM .gitattributes, never from a constant here: two
# places naming one driver is the defect `tools/dupes.sh` exists to count.
declared_driver() {             # -> the merge driver .gitattributes names, or ''
  awk '/^docs\/backlog\/INDEX\.md/ {
         for (i = 1; i <= NF; i++) if ($i ~ /^merge=/) { sub(/^merge=/, "", $i); print $i }
       }' "$CLONE/.gitattributes" 2>/dev/null | head -1
}

# CONFIG IS PER-CLONE, AND NOBODY CONFIGURES IT.  Measured: two rebase
# conflicts in one day for one lane, on a file that is GENERATED — and a fix
# that needs a human to type it is not a fix.  So the gates call this on their
# first run in a clone.  0 when it configured something (and said so), 1 when
# there was nothing to do — silence is the normal case.
ensure_driver() {
  local name cur
  name="$(declared_driver)"
  [ -n "$name" ] || return 1                    # nothing declared: nothing to do
  git -C "$CLONE" rev-parse --git-dir >/dev/null 2>&1 || return 1
  cur="$(git -C "$CLONE" config --get "merge.$name.driver" 2>/dev/null || true)"
  [ -n "$cur" ] && return 1                     # already set: stay silent
  git -C "$CLONE" config "merge.$name.driver" true 2>/dev/null || return 1
  echo "  merge driver: configured merge.$name.driver=true — .gitattributes names it and git does not ship it, so docs/backlog/INDEX.md will resolve instead of conflicting"
  return 0
}

rows() {                        # -> "sortkey\tid\ttitle\tlane"
  local f base
  for f in "$DIR"/*.md; do
    [ -f "$f" ] || continue
    base="$(basename "$f")"
    case "$base" in INDEX.md) continue ;; esac
    awk -v lane="${base%.md}" '
      /^## / {
        line = substr($0, 4)
        id = line; sub(/[ \t].*$/, "", id)
        title = line
        if (index(title, " — ") > 0) sub(/^[^—]*— */, "", title)
        else sub(/^[^ ]+ */, "", title)
        gsub(/\r/, "", title)
        # `YYYY-MM-DD-<lane>-<n>` -> a key that sorts by date then NUMBER.
        if (id ~ /^[0-9]{4}-[0-9]{2}-[0-9]{2}-.*-[0-9]+$/) {
          date = substr(id, 1, 10)
          n = id; sub(/^.*-/, "", n)
          key = sprintf("%s %04d", date, n)
        } else {
          key = "0000-00-00 0000"      # undated: sorts LAST, and is flagged
        }
        printf "%s\t%s\t%s\t%s\n", key, id, title, lane
      }' "$f"
  done
}

render() {
  local total lanes undated
  total="$(rows | grep -c .)"
  lanes="$(rows | awk -F'\t' '{print $4}' | sort -u | grep -c .)"
  undated="$(rows | awk -F'\t' '$1 ~ /^0000/' | grep -c .)"
  cat <<HDR
# The backlog INDEX — every lane's entries, newest first

**GENERATED by \`tools/backlog-index.sh\`. Do not hand-edit.** §9.5 makes the
index generated rather than maintained, which is §5.5's *"generated and
checked, never hand-maintained"* applied to the repository's own record.

**CONFLICT? REGENERATE with \`tools/backlog-index.sh\` — never merge.** A
merged generated file is a third version that matches neither tree;
\`.gitattributes\` marks this file \`merge=ours\` so a rebase resolves without
one (install the driver once with
\`tools/backlog-index.sh --install-merge-driver\`).

Entries live in \`docs/backlog/<lane>.md\`, appended only by their own lane,
with ids \`YYYY-MM-DD-<lane>-<n>\` that need no reservation. Everything before
the split is in [\`docs/backlog-archive.md\`](../backlog-archive.md), frozen,
and every existing \`§Lnn\` reference still resolves there.

**$total entries across $lanes lanes.** Regenerate with
\`tools/backlog-index.sh\`; check with \`--check\` (exit 1 on drift).

| id | title | lane |
| --- | --- | --- |
HDR
  rows | LC_ALL=C sort -r | awk -F'\t' '{ printf "| `%s` | %s | %s |\n", $2, $3, $4 }'
  if [ "$undated" != "0" ]; then
    printf '\n**%s heading(s) do not use the §9.5 id scheme** and sort last.\n' "$undated"
  fi
}

# --------------------------------------------------------------- self-test
if [ "$MODE" = "self-test" ]; then
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/blindex-selftest.XXXXXX")" || die "no temp dir"
  trap 'rm -rf "$tmp"' EXIT
  ok=0; bad=0
  check() { if [ "$2" = "$3" ]; then ok=$((ok+1)); echo "  ok   $1"; \
            else bad=$((bad+1)); echo "  FAIL $1: got '$2' want '$3'"; fi; }

  mkdir -p "$tmp/bl"
  DIR="$tmp/bl"
  cat > "$tmp/bl/alpha.md" <<'MD'
# The alpha lane
## 2026-08-20-alpha-1 — the first thing
body
## 2026-08-22-alpha-2 — the second thing
body
MD
  cat > "$tmp/bl/beta.md" <<'MD'
# The beta lane
## 2026-08-21-beta-1 — a beta thing
## 2026-08-22-beta-10 — the TENTH, which must outrank the second
MD

  check "every entry becomes a row"    "$(rows | grep -c .)" "4"
  check "the lane comes from the FILE" "$(rows | awk -F'\t' '$2=="2026-08-21-beta-1"{print $4}')" "beta"
  check "the title is the em-dash tail" "$(rows | awk -F'\t' '$2=="2026-08-20-alpha-1"{print $3}')" "the first thing"
  # The trap a lexicographic sort walks into: `-10` must beat `-2`.
  check "newest first, and 10 > 2 NUMERICALLY" \
        "$(rows | LC_ALL=C sort -r | head -1 | awk -F'\t' '{print $2}')" "2026-08-22-beta-10"
  check "  ...with the same-day sibling next" \
        "$(rows | LC_ALL=C sort -r | sed -n 2p | awk -F'\t' '{print $2}')" "2026-08-22-alpha-2"
  check "the oldest sorts last" \
        "$(rows | LC_ALL=C sort -r | tail -1 | awk -F'\t' '{print $2}')" "2026-08-20-alpha-1"

  # An UNDATED heading is flagged, never dropped.
  printf '## G1 — an undated drifter\n' >> "$tmp/bl/beta.md"
  check "a drifter still yields a row"   "$(rows | grep -c .)" "5"
  check "  ...and is flagged in the page" "$(render | grep -c 'do not use the §9.5 id scheme')" "1"
  check "  ...and sorts LAST"             "$(rows | LC_ALL=C sort -r | tail -1 | awk -F'\t' '{print $2}')" "G1"
  sed -i.bak '$d' "$tmp/bl/beta.md"; rm -f "$tmp/bl/beta.md.bak"

  check "the page counts entries and lanes" "$(render | grep -c '\*\*4 entries across 2 lanes\.\*\*')" "1"
  check "the page says GENERATED"           "$(render | grep -c 'GENERATED by')" "1"
  check "INDEX.md is not its own input"     "$(printf '# x\n## 2026-01-01-x-1 — x\n' > "$tmp/bl/INDEX.md"; rows | grep -c .)" "4"

  # §5.4's double-run clause, on the generator.
  check "double run is byte-identical" \
        "$( [ "$(render | shasum | cut -d' ' -f1)" = "$(render | shasum | cut -d' ' -f1)" ] && echo same)" "same"

  # --check must FAIL on drift and pass in sync: both directions (MEAS-42).
  render > "$tmp/bl/INDEX.md"
  check "in sync, --check is quiet"  "$(diff -q <(render) "$tmp/bl/INDEX.md" >/dev/null && echo insync)" "insync"
  printf '\nhand-edited\n' >> "$tmp/bl/INDEX.md"
  check "drifted, --check notices"   "$(diff -q <(render) "$tmp/bl/INDEX.md" >/dev/null && echo insync)" ""

  # ---- the merge driver.  `ours` is NOT built in, so BOTH halves are tested:
  # the .gitattributes line git actually parses, and the config without which
  # that line does nothing.
  echo "  -- merge driver"
  check "the shipped .gitattributes targets INDEX.md" \
        "$(git -C "$CLONE" check-attr merge -- docs/backlog/INDEX.md 2>/dev/null | awk '{print $NF}')" "backlog-index"
  check "and it is not set on an ordinary doc" \
        "$(git -C "$CLONE" check-attr merge -- docs/law-index.md 2>/dev/null | awk '{print $NF}')" "unspecified"

  mr="$tmp/mergerepo"
  mkdir -p "$mr" && git init -q "$mr" 2>/dev/null
  git -C "$mr" config user.email qol@example && git -C "$mr" config user.name qol
  printf 'docs/backlog/INDEX.md merge=backlog-index\n' > "$mr/.gitattributes"
  mkdir -p "$mr/docs/backlog"
  printf 'base\n' > "$mr/docs/backlog/INDEX.md"
  git -C "$mr" add -A && git -C "$mr" commit -qm base
  base_branch="$(git -C "$mr" rev-parse --abbrev-ref HEAD)"
  git -C "$mr" checkout -q -b side
  printf 'a side entry\n' >> "$mr/docs/backlog/INDEX.md"
  git -C "$mr" commit -qam side
  git -C "$mr" checkout -q "$base_branch"
  printf 'our entry\n' >> "$mr/docs/backlog/INDEX.md"
  git -C "$mr" commit -qam ours

  # WITHOUT the config: the attribute alone does nothing.
  git -C "$mr" merge side >/dev/null 2>&1
  check "WITHOUT the driver configured it still conflicts" \
        "$(grep -c '<<<<<<<' "$mr/docs/backlog/INDEX.md")" "1"
  git -C "$mr" merge --abort >/dev/null 2>&1

  # WITH the config: resolves to ours, no conflict, stale-but-valid.
  git -C "$mr" config merge.backlog-index.driver true
  git -C "$mr" merge side >/dev/null 2>&1
  check "WITH the driver the merge succeeds"  "$?" "0"
  check "  ...taking OUR side"                "$(tail -1 "$mr/docs/backlog/INDEX.md")" "our entry"
  check "  ...and never a merged THIRD version" \
        "$(grep -c 'a side entry' "$mr/docs/backlog/INDEX.md")" "0"
  check "the config the driver needs is set"  "$(git -C "$mr" config --get merge.backlog-index.driver)" "true"

  # The installer's OWN output.  Its first version had backticks inside a
  # double-quoted echo, so the shell ran `ours` and printed "command not
  # found" into an otherwise successful install.  Tested now, not admired.
  inst="$(bash "$CLONE/tools/backlog-index.sh" --dir "$mr" --install-merge-driver 2>&1)"
  check "the installer reports success"       "$(printf '%s' "$inst" | grep -c 'merge.ours.driver=true set')" "1"
  check "  ...and prints NO shell errors"     "$(printf '%s' "$inst" | grep -ci 'command not found\|No such file\|unbound')" "0"

  check "the header says what to do on a conflict" \
        "$(render | grep -c 'CONFLICT? REGENERATE')" "1"

  # ---- the driver the gates auto-configure, because config is per-clone
  echo "  -- ensure-driver"
  ed="$tmp/ed"; mkdir -p "$ed"; git init -q "$ed" 2>/dev/null
  saved="$CLONE"; CLONE="$ed"
  check "nothing declared -> nothing done"   "$(ensure_driver; echo $?)" "1"
  printf 'docs/backlog/INDEX.md merge=backlog-index\n' > "$ed/.gitattributes"
  check "the driver NAME is read from .gitattributes" "$(declared_driver)" "backlog-index"
  out="$(ensure_driver)"; rc=$?
  check "declared but unset -> configures it"  "$rc" "0"
  check "  ...and says so in one line"         "$(printf '%s' "$out" | grep -c 'merge.backlog-index.driver=true')" "1"
  check "  ...and git really has it"           "$(git -C "$ed" config --get merge.backlog-index.driver)" "true"
  check "already set -> SILENT"                "$(ensure_driver)" ""
  check "  ...and reports nothing to do"       "$(ensure_driver; echo $?)" "1"
  printf 'docs/backlog/INDEX.md merge=other-name\n' > "$ed/.gitattributes"
  check "a RENAMED driver is followed"         "$(declared_driver)" "other-name"
  ensure_driver >/dev/null
  check "  ...and configured under its new name" "$(git -C "$ed" config --get merge.other-name.driver)" "true"
  CLONE="$saved"

  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

[ -d "$DIR" ] || die "no backlog directory at '$DIR'"
OUT="$DIR/INDEX.md"

case "$MODE" in
  ensure-driver)
    ensure_driver || true ;;
  install-driver)
    git -C "$CLONE" rev-parse --git-dir >/dev/null 2>&1 || die "'$CLONE' is not a git clone"
    git -C "$CLONE" config merge.ours.driver true || die "could not set merge.ours.driver"
    echo "backlog-index.sh: merge.ours.driver=true set in $CLONE"
    echo "  docs/backlog/INDEX.md now resolves to OUR side on a rebase instead of"
    echo "  conflicting.  The result is stale-but-valid: run tools/backlog-index.sh."
    echo "  (Without this config, the merge=ours attribute does nothing: ours is"
    echo "  not one of git's built-in drivers — those are text, binary, union.)" ;;
  stdout) render ;;
  check)
    if [ ! -f "$OUT" ]; then
      echo "backlog-index.sh: DRIFT — $OUT does not exist; run tools/backlog-index.sh" >&2
      exit 1
    fi
    if render | diff -q - "$OUT" >/dev/null 2>&1; then
      echo "backlog-index.sh: in sync ($(rows | grep -c .) entries)"
    else
      echo "backlog-index.sh: DRIFT — $OUT is stale; run tools/backlog-index.sh" >&2
      render | diff - "$OUT" | head -12 >&2
      exit 1
    fi ;;
  write)
    render > "$OUT" || die "cannot write '$OUT'"
    echo "backlog-index.sh: wrote $OUT ($(rows | grep -c .) entries)" ;;
esac
