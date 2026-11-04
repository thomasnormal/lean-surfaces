# tools/lakeinfo.sh — what the LAKEFILE says a library is, in one place.
#
# Sourced, not executed.  `check.sh` read `lakefile.toml` and correctly called
# a repo-root `.lean` SCRATCH (the `Examples.+` glob does not match a root
# module, and the `LeanModels` lib's root is `LeanModels.lean` itself);
# `triad.sh` hard-coded `LeanModels/*|Examples/*` and warned "UNSTAGED LEAN
# UNDER A LAKE GLOB" about the same file.  It warned rather than refused, so
# it was safe — but two protocol tools disagreeing about one file eventually
# gets trusted in the wrong direction.
#
# So the glob source is READ ONCE, here, by both.  A second parser is the
# defect `tools/dupes.sh` counts (MEAS-28).
#
#   lake_lib_roots <clone>   -> the [[lean_lib]] names and [[lean_exe]] roots
#   lake_glob_class <clone> <repo-relative-path> -> library | scratch

lake_lib_roots() {              # clone -> one library/exe root name per line
  local f="${1:?}/lakefile.toml"
  [ -f "$f" ] || return 0
  awk '
    /^\[\[lean_lib\]\]/  { sec = "lib"; next }
    /^\[\[lean_exe\]\]/  { sec = "exe"; next }
    /^\[\[/              { sec = "";    next }
    sec == "lib" && /^[ \t]*name[ \t]*=/ { print val($0); next }
    sec == "exe" && /^[ \t]*root[ \t]*=/ { print val($0); next }
    function val(l) { sub(/^[^=]*=[ \t]*/, "", l); gsub(/["\047 \t\r]/, "", l); return l }
  ' "$f"
}

lake_glob_class() {             # clone, path -> library | scratch
  local clone="${1:?}" p="${2:?}" root top
  for root in $(lake_lib_roots "$clone"); do
    top="${root%%.*}"           # `LeanModels.Circuit.DCRunner` -> `LeanModels`
    [ -n "$top" ] || continue
    case "$p" in
      "$top".lean|"$top"/*) echo library; return 0 ;;
    esac
  done
  echo scratch
}
