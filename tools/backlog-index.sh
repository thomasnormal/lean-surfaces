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
# THE MERGE DRIVER.  Merging a generated file line-by-line is always wrong: a
# text-merged index is a THIRD version matching neither tree.  `.gitattributes`
# marks this file `merge=backlog-index`, and each clone must define that driver
# or git falls back to a normal conflict.  Measured both ways.
#
# IT MERGES THE ROWS, AND IT CANNOT MERGE THE SOURCES.  Git hands a driver
# three versions of THIS FILE — `%A` ours, `%O` base, `%B` theirs — and nothing
# else.  It does not hand it the merged per-lane files, and it runs BEFORE the
# merged sources reach the working tree.  A driver that re-runs the generator
# therefore regenerates from the ONTO side's sources and reproduces the very
# drop it was written to fix: measured, 3 rows of 4, identical to the old
# resolve-to-one-side behaviour and harder to doubt because it looks
# authoritative.  The rows, however, are all present across `%A` and `%B`.
#
#   tools/backlog-index.sh --strict     # exit 3 on a MALFORMED heading
#
# EXIT  0 in sync (or written)   1 drift (--check)   2 refusal
#       3 a heading a lane cannot see: `## <sentence>` becomes a JUNK ID
#
# ZERO Lean execution.  Safe outside a tenure (A11).

set -u

CLONE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DIR=""
MODE="write"
STRICT=0
MD_A=""; MD_O=""; MD_B=""

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
    --merge-driver)
      # THREE values, so the two-argument guard is not the right one.
      [ $# -ge 4 ] || die "--merge-driver needs three paths (%A %O %B)"
      MODE="merge-driver"; MD_A="$2"; MD_O="$3"; MD_B="$4"; shift 4 ;;
    --ensure-driver)        MODE="ensure-driver"; shift ;;
    --strict)    STRICT=1; shift ;;
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
  [ "$cur" = "$DRIVER_CMD" ] && return 1        # already correct: stay silent
  git -C "$CLONE" config "merge.$name.driver" "$DRIVER_CMD" 2>/dev/null || return 1
  # AN UPGRADE, NOT ONLY AN INSTALL.  Every clone that ran an earlier gate has
  # `driver=true`, which RESOLVES TO ONE SIDE and drops the other's rows.  If
  # this only acted on an unset key the fix would never reach the clones that
  # already have the broken one — and config is per-clone, so nothing else
  # would.  FIXES LIVE IN GATES.
  if [ -n "$cur" ]; then
    # SAY WHAT THE OLD VALUE ACTUALLY WAS.  `true` is the one that dropped
    # rows; any other stale value is a version skew, and claiming it dropped
    # rows would be a confident sentence about something unmeasured.
    if [ "$cur" = "true" ]; then
      echo "  merge driver: UPGRADED merge.$name.driver (was 'true', which resolved docs/backlog/INDEX.md to ONE side and dropped the other lane's rows) — it now merges the ROWS"
    else
      echo "  merge driver: UPGRADED merge.$name.driver (was '$cur') — refreshed to the current row-merging command"
    fi
  else
    echo "  merge driver: configured merge.$name.driver — .gitattributes names it and git does not ship it, so docs/backlog/INDEX.md merges its ROWS instead of conflicting"
  fi
  return 0
}

# RELATIVE ON PURPOSE.  git runs a merge driver with the working tree's
# toplevel as its cwd (measured), and `.git/config` is SHARED BY EVERY LINKED
# WORKTREE — so an absolute path baked in here would point one worktree's merge
# at another worktree's script.  A relative path is the portable one.
# `|| true` IS LOad-BEARING, and a rebase taught it.  git runs the driver from
# the WORKING TREE, which mid-rebase holds the ONTO side's script -- so while
# rebasing onto any commit that predates `--merge-driver`, the configured
# command reaches a script that refuses the flag and exits 2.  A non-zero
# driver HALTS (measured), so upgrading a clone's config would have halted
# every rebase onto older history, in every clone, until this landed.  The
# never-halt rule cannot live only INSIDE the script: the script is exactly
# what version skew replaces.  `|| true` puts it in the CONFIG, where skew
# cannot reach it -- an old script then resolves to ours, which is what it did
# before, and the stderr line still prints.
DRIVER_CMD='tools/backlog-index.sh --merge-driver %A %O %B || true'

merge_driver() {                # ours base theirs -> the union of rows, into ours
  # THE ROWS ARE THE MERGE.  Both sides are renderings of the same generator,
  # so every row is a self-contained record and the union of the two sides
  # contains every entry either lane wrote.  Nothing is read from the working
  # tree, which is what makes this correct where re-running the generator is
  # not.
  #
  # NAMED FAILURE MODE — A RETITLE YIELDS A SUPERSET.  If one side re-words an
  # existing entry's title, both the old and the new row survive the union: the
  # index is then a stale SUPERSET, never a subset.  That is the deliberate
  # trade.  A superset LOSES NOTHING and the next `tools/backlog-index.sh`
  # regenerates it exactly; a subset silently deletes another lane's record.
  #
  # AND IT NEVER EXITS NON-ZERO.  Measured: a driver that fails HALTS the
  # rebase — git treats a non-zero driver as a conflict, so a broken driver
  # would stop every lane's rebase in every clone.  So every failure path here
  # LEAVES OUR SIDE IN PLACE and returns 0, which is exactly the old
  # behaviour: never worse than before the driver existed.  That is safe only
  # because the stale index it leaves is REFUSED by the floor — the docs floor
  # runs `--check` (2026-08-26).  The fallback and that gate are one design;
  # neither is sound alone.  The failure is never silent: it says so on stderr.
  local ours="${1:-}" theirs="${3:-}" tmp
  if [ ! -r "$ours" ] || [ ! -r "$theirs" ]; then
    echo "backlog-index.sh: MERGE DRIVER could not read its inputs — left OUR side in place." >&2
    echo "  The index is STALE: run tools/backlog-index.sh.  The docs floor's --check refuses it." >&2
    return 0
  fi
  if ! grep -q '^| --- ' "$ours"; then
    echo "backlog-index.sh: MERGE DRIVER found no table header in ours — left OUR side in place." >&2
    echo "  The index is STALE: run tools/backlog-index.sh.  The docs floor's --check refuses it." >&2
    return 0
  fi
  tmp="$(mktemp "${TMPDIR:-/tmp}/backlog-merge.XXXXXX")" || {
    echo "backlog-index.sh: MERGE DRIVER could not make a temp file — left OUR side in place." >&2
    return 0; }
  {
    sed -n '1,/^| --- /p' "$ours"
    # THE SAME KEY THE GENERATOR SORTS BY (date, then NUMBER — `-10` must beat
    # `-2`), recomputed from the rendered id.  The id is the FIRST backtick
    # pair, which is why splitting on a backtick is safe even though titles
    # contain them.
    # NOT `sort -u`.  The real index legitimately carries BYTE-IDENTICAL rows
    # -- two lanes wrote entries that render the same, and there are two such
    # pairs in it today -- so deduping by row TEXT silently deletes them:
    # measured, 424 rows owed and 422 delivered, and the fixtures could not see
    # it because a synthetic index has no duplicates.  This is a THREE-way
    # merge and %O is available, so take OURS whole (multiplicity and all) and
    # add only what THEIRS has that ours does not.  `comm` respects
    # multiplicity; `sort -u` cannot.
    { grep '^| `' "$ours"
      LC_ALL=C comm -13 <(grep '^| `' "$ours"   | LC_ALL=C sort) \
                        <(grep '^| `' "$theirs" | LC_ALL=C sort)
    } | awk -F'`' '{
        id = $2
        if (id ~ /^[0-9]{4}-[0-9]{2}-[0-9]{2}-.*-[0-9]+$/) {
          date = substr(id, 1, 10); n = id; sub(/^.*-/, "", n)
          key = sprintf("%s %04d", date, n)
        } else { key = "0000-00-00 0000" }
        printf "%s\t%s\n", key, $0
      }' | LC_ALL=C sort -r | cut -f2-
    # whatever ours carries AFTER the table (the undated-ids footer)
    awk '/^\| `/ { seen = 1; next } seen { print }' "$ours"
  } > "$tmp" 2>/dev/null || {
    rm -f "$tmp"
    echo "backlog-index.sh: MERGE DRIVER failed while merging rows — left OUR side in place." >&2
    echo "  The index is STALE: run tools/backlog-index.sh.  The docs floor's --check refuses it." >&2
    return 0; }
  mv "$tmp" "$ours" 2>/dev/null || { rm -f "$tmp"
    echo "backlog-index.sh: MERGE DRIVER could not write the result — left OUR side in place." >&2
    return 0; }
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
        # THE CLASS COMES FROM THE TITLE PREFIX (§9.5a, resolved).  It used to
        # come from the id token, which is exactly why the convention and the
        # id law collided: `INBOUND` cannot be both the class and the id.  The
        # id token is still honoured so the SIX headings still in the original
        # spelling keep their class while the lanes that own them re-spell.
        cls = ""
        if (title ~ /^INBOUND([^A-Za-z0-9_]|$)/) cls = "INBOUND"
        else if (id == "INBOUND")                cls = "INBOUND"
        printf "%s\t%s\t%s\t%s\t%s\n", key, id, title, lane, cls
      }' "$f"
  done
}

# THE SHAPE THIS FILE SILENTLY ACCEPTS (the analog founding, 2026-08).
#
# `rows` takes the FIRST TOKEN of every `## ` heading as an id.  Given a
# structural heading — `## Phase 1`, `## Notes` — it invents the id `Phase` or
# `Notes` and emits a row nobody wrote: the analog lane produced 246 entries
# with three junk ids before conforming its headings by hand.  The sensitivity
# was real and unadvertised, and THE GENERATOR'S SILENT ACCEPTANCE IS THE
# DEFECT, not the lane's headings.
#
# THREE VERDICTS, because the tree holds three different things (measured
# 2026-08-24: 18 undated, 8 malformed, across 7 lane files):
#
#   conforming   `<id> — <title>` with a dated §9.5 id
#   undated      `<id> — <title>` whose id is not dated — the Go lane's
#                historical `G1`…`G18`.  Real entries, ALREADY flagged and
#                sorted last; a warning, never a failure, or `--strict` could
#                never be adopted while they exist.
#   malformed    no ` — ` at all, or a MULTI-WORD phrase before it, so the id
#                is a word lifted out of a sentence.  This is the junk-id
#                family, and it is what --strict fails on.
#
# The discriminator is the token count before the em dash: an id is ONE token.
# `INBOUND FROM THE SOFTFLOAT LANE — …` is five, and yields the id `INBOUND`.
heading_rows() {                # -> "verdict<TAB>file:line<TAB>heading"
  local f base
  for f in "$DIR"/*.md; do
    [ -f "$f" ] || continue
    base="$(basename "$f")"
    case "$base" in INDEX.md) continue ;; esac
    awk -v F="$f" '
      /^## / {
        line = substr($0, 4); gsub(/\r/, "", line)
        has = (index(line, " — ") > 0)
        pre = line; if (has) sub(/ — .*$/, "", pre)
        n = split(pre, w, /[ \t]+/)
        dated = (w[1] ~ /^[0-9]{4}-[0-9]{2}-[0-9]{2}-.*-[0-9]+$/)
        # OLD-VALID: §9.5a told filers to head the entry `INBOUND`, so these
        # are malformed BECAUSE THE CHARTER SAID SO.  They warn and never
        # fail, which is the migration vocabulary — a shape the rules once
        # required cannot be a failure the day a new rule lands.
        v = (has && n == 1) ? (dated ? "conforming" : "undated") \
            : ((w[1] == "INBOUND") ? "old-valid" : "malformed")
        printf "%s\t%s:%d\t%s\n", v, F, NR, substr(line, 1, 60)
      }' "$f"
  done
}

# LOUD, ON STDERR, NAMING THE FILE AND THE HEADING.  The old report was a
# COUNT inside the generated file — a place the lane that wrote the heading
# never looks.  A warning nobody is shown is not a warning.
heading_report() {              # -> 0 clean, 3 when a malformed heading exists
  local rows mal und old
  rows="$(heading_rows)"
  mal="$(printf '%s\n' "$rows" | awk -F'\t' '$1 == "malformed"' | grep -c . || true)"
  und="$(printf '%s\n' "$rows" | awk -F'\t' '$1 == "undated"' | grep -c . || true)"
  old="$(printf '%s\n' "$rows" | awk -F'\t' '$1 == "old-valid"' | grep -c . || true)"
  if [ "$mal" != "0" ]; then
    echo "backlog-index.sh: $mal heading(s) are not \`## <id> — <title>\`, so this generator" >&2
    echo "  INVENTS an id from the first word and emits a row the lane never wrote:" >&2
    printf '%s\n' "$rows" | awk -F'\t' '$1 == "malformed" { printf "    %s\n      ## %s\n", $2, $3 }' >&2
    echo "  Give each one a §9.5 id (\`YYYY-MM-DD-<lane>-<n>\`) before the em dash." >&2
  fi
  [ "$und" = "0" ] || echo "backlog-index.sh: $und heading(s) use a non-dated id (flagged in the index, sorted last)" >&2
  if [ "$old" != "0" ]; then
    echo "backlog-index.sh: $old INBOUND heading(s) use §9.5a's ORIGINAL spelling (old-valid — warn, never fail)." >&2
    echo "  The id now goes FIRST and INBOUND moves into the title (§9.5a, resolved):" >&2
    echo "    ## <sender-id> — INBOUND FROM THE <X> LANE: <what the owner should do>" >&2
    echo "  The index classes them by TITLE PREFIX, so the INBOUND column survives the move." >&2
  fi
  [ "$mal" = "0" ] || return 3
  return 0
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

**CONFLICT? REGENERATE with \`tools/backlog-index.sh\` — never hand-merge.** A
line-merged generated file is a third version that matches neither tree.
\`.gitattributes\` marks this file \`merge=backlog-index\`, a driver that merges
the table's ROWS so no lane's entries are dropped (the gates configure it; by
hand it is \`tools/backlog-index.sh --install-merge-driver\`).  A retitle can
leave a stale superset — regenerating fixes it exactly.

Entries live in \`docs/backlog/<lane>.md\`, appended only by their own lane,
with ids \`YYYY-MM-DD-<lane>-<n>\` that need no reservation. Everything before
the split is in [\`docs/backlog-archive.md\`](../backlog-archive.md), frozen,
and every existing \`§Lnn\` reference still resolves there.

**$total entries across $lanes lanes.** Regenerate with
\`tools/backlog-index.sh\`; check with \`--check\` (exit 1 on drift).

| id | class | title | lane |
| --- | --- | --- | --- |
HDR
  rows | LC_ALL=C sort -r | awk -F'\t' '{ printf "| `%s` | %s | %s | %s |\n", $2, $5, $3, $4 }'
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
  # A DRIFTER IS A WARNING, NEVER A FAILURE.  The Go lane's `G1`…`G18` are
  # real entries under an older scheme; if --strict failed on them it could
  # never be turned on, and a flag nobody can turn on is not a gate.
  check "an undated id WARNS"            "$(heading_report 2>&1 >/dev/null | grep -c 'non-dated id')" "1"
  check "  ...and does NOT fail strict"  "$(heading_report >/dev/null 2>&1; echo $?)" "0"
  sed -i.bak '$d' "$tmp/bl/beta.md"; rm -f "$tmp/bl/beta.md.bak"

  # ---- THE MALFORMED SHAPE (the analog founding): a heading with no id at
  # all, from which this generator INVENTS one out of the first word.
  # SNAPSHOT AND RESTORE, never `sed '$d'` per appended line: `$d;$d;$d`
  # deletes ONE line, because `d` restarts the cycle and the later commands
  # never run.  The first cut left two lines behind and three later rows read
  # a tree nobody meant to build.
  cp "$tmp/bl/beta.md" "$tmp/bl/beta.orig"
  printf '## Phase 1\n\ntext\n' >> "$tmp/bl/beta.md"
  check "a structural heading is MALFORMED" "$(heading_rows | awk -F'\t' '$1=="malformed"' | grep -c .)" "1"
  check "  ...and the generator still invents an id" \
        "$(rows | awk -F'\t' '{print $2}' | grep -c '^Phase$')" "1"
  out="$(heading_report 2>&1 >/dev/null)"
  check "  ...the warning NAMES the file"   "$(printf '%s' "$out" | grep -c 'beta.md:')" "1"
  check "  ...and quotes the heading"       "$(printf '%s' "$out" | grep -c '## Phase 1')" "1"
  check "  ...and says what to write"       "$(printf '%s' "$out" | grep -c 'YYYY-MM-DD')" "1"
  check "  ...and it is NOT dropped"        "$(rows | grep -c .)" "5"
  check "malformed exits 3"                 "$(heading_report >/dev/null 2>&1; echo $?)" "3"
  # A MULTI-WORD PHRASE before the em dash is the SAME defect wearing a title:
  # `INBOUND FROM THE SOFTFLOAT LANE — …` yields the id `INBOUND`.  Eight of
  # these are live in the tree, which is why --strict is opt-in.
  cp "$tmp/bl/beta.orig" "$tmp/bl/beta.md"
  printf '## INBOUND FROM SOMEWHERE — `2026-01-01-x-9` (a note)\n' >> "$tmp/bl/beta.md"
  # §9.5a's ORIGINAL spelling is OLD-VALID, not malformed: the charter told
  # filers to write it that way, and a shape the rules once REQUIRED cannot be
  # a failure the day a new rule lands.
  check "the old INBOUND spelling is OLD-VALID" "$(heading_rows | awk -F'\t' '$1=="old-valid"' | grep -c .)" "1"
  check "  ...and does NOT fail --strict"   "$(heading_report >/dev/null 2>&1; echo $?)" "0"
  check "  ...while keeping its INBOUND class" "$(rows | awk -F'\t' '$5=="INBOUND"' | grep -c .)" "1"
  check "  ...and the warning shows the NEW shape" \
        "$(heading_report 2>&1 >/dev/null | grep -c 'id now goes FIRST')" "1"
  # ...but a multi-word heading that is NOT the known convention is still junk.
  cp "$tmp/bl/beta.orig" "$tmp/bl/beta.md"
  printf '## SPEC COVERAGE — the completion metric (standing)\n' >> "$tmp/bl/beta.md"
  check "another multi-word phrase is malformed" "$(heading_rows | awk -F'\t' '$1=="malformed"' | grep -c .)" "1"
  check "  ...and DOES fail --strict"       "$(heading_report >/dev/null 2>&1; echo $?)" "3"

  # ---- THE RESOLVED SHAPE (§9.5a): id first, INBOUND in the TITLE.
  cp "$tmp/bl/beta.orig" "$tmp/bl/beta.md"
  printf '## 2026-01-01-x-9 — INBOUND FROM THE X LANE: renumber or close\n' >> "$tmp/bl/beta.md"
  check "the new shape is CONFORMING"       "$(heading_rows | awk -F'\t' '$1=="conforming"' | grep -c .)" "5"
  check "  ...nothing malformed or old"     "$(heading_rows | awk -F'\t' '$1!="conforming"' | grep -c .)" "0"
  check "  ...and the run is silent"        "$(heading_report 2>&1 >/dev/null | grep -c .)" "0"
  check "  ...exiting clean under --strict" "$(heading_report >/dev/null 2>&1; echo $?)" "0"
  # THE CLASS SURVIVES THE MOVE, which is the whole point of the resolution.
  check "the class comes from the TITLE now" "$(rows | awk -F'\t' '$5=="INBOUND"' | grep -c .)" "1"
  check "  ...on a row whose id is the SENDER's" \
        "$(rows | awk -F'\t' '$5=="INBOUND" {print $2}')" "2026-01-01-x-9"
  check "  ...and the page renders the column" "$(render | grep -c '| id | class | title | lane |')" "1"
  check "  ...with INBOUND in it"           "$(render | grep -c '| `2026-01-01-x-9` | INBOUND |')" "1"

  # MIXED, which is what the migration window actually looks like: one row in
  # the old spelling (warn) beside one in the new (clean) — and --strict PASSES.
  printf '## INBOUND FROM SOMEWHERE — `2026-01-01-x-8` (a note)\n' >> "$tmp/bl/beta.md"
  check "mixed old-valid + new-shape warns"  "$(heading_report 2>&1 >/dev/null | grep -c 'old-valid')" "1"
  check "  ...and --strict still PASSES"    "$(heading_report >/dev/null 2>&1; echo $?)" "0"
  check "  ...with BOTH classed INBOUND"    "$(rows | awk -F'\t' '$5=="INBOUND"' | grep -c .)" "2"
  cp "$tmp/bl/beta.orig" "$tmp/bl/beta.md"; rm -f "$tmp/bl/beta.orig"
  check "a conforming tree warns about nothing" "$(heading_report 2>&1 >/dev/null | grep -c .)" "0"
  check "  ...and exits clean"              "$(heading_report >/dev/null 2>&1; echo $?)" "0"

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

  # A REAL-FORMAT FIXTURE.  The first version of these rows used a plain-text
  # INDEX.md ("base", "our entry"), and with a ROW-merging driver that file has
  # no table header -- so every row passed through the driver's FALLBACK path
  # and asserted nothing about merging.  A fixture that cannot exercise the
  # mechanism tests the fixture.
  mkdriver_repo() {             # $1 = dir; builds two lanes that both regenerate
    local d="$1"
    rm -rf "$d"; mkdir -p "$d/docs/backlog"
    git init -q -b main "$d" 2>/dev/null
    git -C "$d" config user.email qol@example; git -C "$d" config user.name qol
    printf 'docs/backlog/INDEX.md merge=backlog-index\n' > "$d/.gitattributes"
    printf '# qol\n\n## 2026-08-20-qol-1 — first qol entry\n' > "$d/docs/backlog/qol.md"
    printf '# sv\n\n## 2026-08-20-sv-1 — first sv entry\n'   > "$d/docs/backlog/sv.md"
    bash "$CLONE/tools/backlog-index.sh" --dir "$d" >/dev/null 2>&1
    git -C "$d" add -A; git -C "$d" commit -qm base
    git -C "$d" config merge.backlog-index.driver "bash $CLONE/tools/backlog-index.sh --merge-driver %A %O %B"
    git -C "$d" checkout -q -b lane
    if [ "${2:-}" = retitle ]; then
      printf '# qol\n\n## 2026-08-20-qol-1 — RETITLED\n' > "$d/docs/backlog/qol.md"
    else
      printf '\n## 2026-08-21-qol-2 — second qol entry\n' >> "$d/docs/backlog/qol.md"
    fi
    bash "$CLONE/tools/backlog-index.sh" --dir "$d" >/dev/null 2>&1
    git -C "$d" add -A; git -C "$d" commit -qm lane
    git -C "$d" checkout -q main
    printf '\n## 2026-08-21-sv-2 — second sv entry\n' >> "$d/docs/backlog/sv.md"
    bash "$CLONE/tools/backlog-index.sh" --dir "$d" >/dev/null 2>&1
    git -C "$d" add -A; git -C "$d" commit -qm main
    git -C "$d" checkout -q lane
  }
  idx_rows() { grep -c '^| `' "$1/docs/backlog/INDEX.md"; }
  has_row()  { grep -c "^| \`$2\`" "$1/docs/backlog/INDEX.md"; }

  # WITHOUT the config the attribute alone does nothing -- git does not ship
  # this driver, so it falls back to an ordinary conflict.
  mr="$tmp/mergerepo"; mkdriver_repo "$mr"
  git -C "$mr" config --unset merge.backlog-index.driver
  git -C "$mr" rebase main >/dev/null 2>&1
  check "WITHOUT the driver configured it still conflicts" \
        "$(grep -c '<<<<<<<' "$mr/docs/backlog/INDEX.md")" "1"
  git -C "$mr" rebase --abort >/dev/null 2>&1

  # THE REBASE DIRECTION.  This is the one that dropped the REBASING lane's own
  # rows: `ours` mid-rebase is the ONTO side.  pyc paid for it three times in a
  # day.
  mkdriver_repo "$mr"
  git -C "$mr" rebase main >/dev/null 2>&1
  check "REBASE keeps BOTH lanes' rows"        "$(idx_rows "$mr")" "4"
  check "  ...the rebasing lane's own entry"   "$(has_row "$mr" 2026-08-21-qol-2)" "1"
  check "  ...and the other lane's"            "$(has_row "$mr" 2026-08-21-sv-2)" "1"
  check "  ...newest first, as generated"      "$(grep -m1 '^| `' "$mr/docs/backlog/INDEX.md" | cut -d'`' -f2)" "2026-08-21-sv-2"

  # THE PULL DIRECTION, which is the SAME driver with ours/theirs swapped --
  # and which dropped the OTHER lanes' rows instead.  Two directions, two
  # different silent 3-of-4s before this.
  mkdriver_repo "$mr"
  git -C "$mr" merge main -m m >/dev/null 2>&1
  check "PULL keeps BOTH lanes' rows"          "$(idx_rows "$mr")" "4"
  check "  ...the other lane's entry"          "$(has_row "$mr" 2026-08-21-sv-2)" "1"

  # THE NAMED FAILURE MODE: a retitle leaves a SUPERSET, never a subset.
  mkdriver_repo "$mr" retitle
  git -C "$mr" rebase main >/dev/null 2>&1
  check "a RETITLE keeps both spellings"       "$(has_row "$mr" 2026-08-20-qol-1)" "2"
  check "  ...so nothing is ever LOST"         "$(grep -c 'RETITLED' "$mr/docs/backlog/INDEX.md")" "1"
  check "  ...and regenerating fixes it exactly" \
        "$(bash "$CLONE/tools/backlog-index.sh" --dir "$mr" >/dev/null 2>&1; has_row "$mr" 2026-08-20-qol-1)" "1"

  # WHY THE DRIVER MAY NEVER EXIT NON-ZERO.  git treats a failing driver as a
  # conflict and STOPS -- it does not fall back -- so a broken driver would
  # halt every lane's rebase in every clone.  Measured here rather than
  # assumed, because the whole fallback design rests on it.
  mkdriver_repo "$mr"
  git -C "$mr" config merge.backlog-index.driver false
  git -C "$mr" rebase main >/dev/null 2>&1
  check "a driver that FAILS halts the rebase"  "$?" "1"
  git -C "$mr" rebase --abort >/dev/null 2>&1

  # ...so every failure path in ours leaves OUR side and returns 0.
  md="$tmp/mdfall"; mkdir -p "$md"
  printf '| id | class | title | lane |\n| --- | --- | --- | --- |\n| `2026-08-20-qol-1` |  | keep me | qol |\n' > "$md/ours"
  cp "$md/ours" "$md/ours.bak"
  err="$(merge_driver "$md/ours" /nope/base /nope/theirs 2>&1)"; rc=$?
  check "unreadable inputs -> exit 0, never halt" "$rc" "0"
  check "  ...leaving OUR side untouched"         "$(cmp -s "$md/ours" "$md/ours.bak" && echo same || echo changed)" "same"
  check "  ...and saying so LOUDLY"               "$(printf '%s' "$err" | grep -c 'MERGE DRIVER could not read')" "1"
  check "  ...naming the gate that refuses it"    "$(printf '%s' "$err" | grep -c 'check')" "1"
  # DUPLICATE ROWS ARE REAL, and `sort -u` deleted them.  Found against the
  # LIVE 422-row index -- 424 owed, 422 delivered -- and invisible to every
  # fixture here, because a synthetic index has no two lanes that happened to
  # render the same row.  Real data is the only place this was visible.
  printf '| id | class | title | lane |\n| --- | --- | --- | --- |\n| `2026-08-20-x-1` |  | dup | x |\n| `2026-08-20-x-1` |  | dup | x |\n' > "$md/dupA"
  cp "$md/dupA" "$md/dupB"
  printf '| `2026-08-21-y-1` |  | only theirs | y |\n' >> "$md/dupB"
  merge_driver "$md/dupA" "$md/dupA" "$md/dupB" >/dev/null 2>&1
  check "identical duplicate rows are PRESERVED" "$(grep -c '2026-08-20-x-1' "$md/dupA")" "2"
  check "  ...while theirs is still added"       "$(grep -c '2026-08-21-y-1' "$md/dupA")" "1"

  printf 'not an index\n' > "$md/plain"; cp "$md/plain" "$md/plain.bak"
  err="$(merge_driver "$md/plain" "$md/ours" "$md/ours" 2>&1)"; rc=$?
  check "no table header -> exit 0, ours kept"    "$rc" "0"
  check "  ...unchanged"                          "$(cmp -s "$md/plain" "$md/plain.bak" && echo same || echo changed)" "same"

  # The installer, which used to set a key NOTHING READ: `merge.ours.driver`
  # while .gitattributes named `backlog-index`.
  inst="$(bash "$CLONE/tools/backlog-index.sh" --dir "$mr" --install-merge-driver 2>&1)"
  check "the installer reports success"       "$(printf '%s' "$inst" | grep -c 'merge.backlog-index.driver set')" "1"
  check "  ...and prints NO shell errors"     "$(printf '%s' "$inst" | grep -ci 'command not found\|No such file\|unbound')" "0"
  check "  ...setting the DECLARED name"      "$(git -C "$mr" config --get merge.backlog-index.driver)" "$DRIVER_CMD"
  check "the driver command is RELATIVE"      "$(printf '%s' "$DRIVER_CMD" | grep -c '^tools/')" "1"
  check "  ...and cannot halt a rebase"       "$(printf '%s' "$DRIVER_CMD" | grep -c '|| true$')" "1"

  # VERSION SKEW, which is the case `|| true` exists for: mid-rebase the tree
  # holds the ONTO side's script, so a clone configured for `--merge-driver`
  # meets a script that has never heard of it.
  old="$tmp/oldscript.sh"
  printf '#!/bin/sh\necho "backlog-index.sh: unknown argument" >&2\nexit 2\n' > "$old"
  chmod +x "$old"
  mkdriver_repo "$mr"
  git -C "$mr" config merge.backlog-index.driver "bash $old --merge-driver %A %O %B || true"
  git -C "$mr" rebase main >/dev/null 2>&1
  check "an OLD script does NOT halt the rebase" "$?" "0"
  check "  ...it resolves to ours, as before"    "$(idx_rows "$mr")" "3"

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
  check "  ...and says so in one line"         "$(printf '%s' "$out" | grep -c 'configured merge.backlog-index.driver')" "1"
  check "  ...and git really has it"           "$(git -C "$ed" config --get merge.backlog-index.driver)" "$DRIVER_CMD"
  check "already set -> SILENT"                "$(ensure_driver)" ""
  check "  ...and reports nothing to do"       "$(ensure_driver; echo $?)" "1"
  printf 'docs/backlog/INDEX.md merge=other-name\n' > "$ed/.gitattributes"
  check "a RENAMED driver is followed"         "$(declared_driver)" "other-name"
  ensure_driver >/dev/null
  check "  ...and configured under its new name" "$(git -C "$ed" config --get merge.other-name.driver)" "$DRIVER_CMD"

  # THE UPGRADE PATH, which is the whole reason this reaches anybody.  Every
  # clone that ran an earlier gate carries `driver=true` -- the setting that
  # DROPS a lane's rows -- and config is per-clone, so nothing but this would
  # ever replace it.  An install-only ensure_driver would have left the bug in
  # every existing clone while looking fixed in a fresh one.
  printf 'docs/backlog/INDEX.md merge=backlog-index\n' > "$ed/.gitattributes"
  git -C "$ed" config merge.backlog-index.driver true
  out="$(ensure_driver)"; rc=$?
  check "an OLD driver=true is UPGRADED"       "$rc" "0"
  check "  ...to the row-merging command"      "$(git -C "$ed" config --get merge.backlog-index.driver)" "$DRIVER_CMD"
  check "  ...saying what it replaced and why" "$(printf '%s' "$out" | grep -c "UPGRADED")" "1"
  check "  ...naming the rows it used to drop" "$(printf '%s' "$out" | grep -c 'dropped the other')" "1"
  check "  ...and then going SILENT"           "$(ensure_driver)" ""
  CLONE="$saved"

  echo "self-test: $ok ok, $bad failed"
  [ "$bad" = "0" ] || exit 1
  exit 0
fi

[ -d "$DIR" ] || die "no backlog directory at '$DIR'"
OUT="$DIR/INDEX.md"

# THE WARNING RUNS ON EVERY GENERATING MODE, because the moment to say "this
# heading will become a junk id" is the moment the id is being made.  It never
# changes what is written: a row is REPORTED, never dropped — a row nobody can
# see is missing is worse than a row with an ugly id.
HEADING_RC=0
case "$MODE" in
  stdout|check|write) heading_report || HEADING_RC=$? ;;
esac

case "$MODE" in
  ensure-driver)
    ensure_driver || true ;;
  merge-driver)
    merge_driver "$MD_A" "$MD_O" "$MD_B"; exit 0 ;;
  install-driver)
    git -C "$CLONE" rev-parse --git-dir >/dev/null 2>&1 || die "'$CLONE' is not a git clone"
    # THE DECLARED NAME, not a hard-coded one.  This used to set
    # `merge.ours.driver` while `.gitattributes` named `backlog-index` and
    # `ensure_driver` configured that — so the installer set a key nothing
    # read, and only the gate's path ever worked.
    dn="$(declared_driver)"; [ -n "$dn" ] || die "no merge driver declared in .gitattributes"
    git -C "$CLONE" config "merge.$dn.driver" "$DRIVER_CMD" || die "could not set merge.$dn.driver"
    echo "backlog-index.sh: merge.$dn.driver set in $CLONE"
    echo "  docs/backlog/INDEX.md now MERGES ITS ROWS instead of conflicting or"
    echo "  resolving to one side.  A retitle can leave a stale superset; run"
    echo "  tools/backlog-index.sh to regenerate exactly." ;;
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

# --strict TURNS THE WARNING INTO A VERDICT, and it is opt-in for one measured
# reason: 8 malformed headings are live across 7 lane files right now, and
# §9.5 makes a lane file appendable only BY ITS OWN LANE — so this cannot be
# made mandatory by the lane that owns none of them.
[ "$STRICT" = "1" ] && [ "$HEADING_RC" != "0" ] && exit "$HEADING_RC"
exit 0
