#!/usr/bin/env bash
# tools/instruments.sh — the MACHINE-WIDE instruments, in one place.
#
# Sourced, never executed.  `check.sh` used these to decide whether a courtesy
# iteration may start; `triad.sh` now uses the same readings to size its build.
# Two tools asking the same question of the machine must ask it the SAME WAY —
# a second copy is the defect `tools/dupes.sh` counts (MEAS-28), and here it
# would be worse than duplication: two throttles disagreeing about whether the
# box is busy is a protocol that contradicts itself.
#
# EVERY READING CARRIES ITS INSTRUMENT.  That is not decoration: an unlabelled
# percentage is what let a HIGH-WATER swap mark pass for a pressure reading for
# a day, and then let a FREE percentage be quoted as an IN-USE one twice more.
# The label is part of the measurement.
#
#   read_load             -> the 1-minute load average
#   read_pressure         -> "<pct-in-use> <instrument>"
#   over A B              -> 0 when A > B, in floating point

read_load() {                   # 1-minute load average
  [ -n "${LS_MOCK_LOAD:-}" ] && { printf '%s\n' "$LS_MOCK_LOAD"; return 0; }
  if [ -r /proc/loadavg ]; then awk '{print $1}' /proc/loadavg; return 0; fi
  sysctl -n vm.loadavg 2>/dev/null | awk '{ gsub(/[{}]/, ""); print $1 }'
}

# ---- WHAT THE POLITENESS LINE MEASURES (the C lane, 2026-08-24)
#
# THIS READ `sysctl vm.swapusage` "used", WHICH IS A HIGH-WATER MARK, NOT A
# PRESSURE READING.  On macOS that figure is swap ALLOCATED AND NOT RECLAIMED:
# once a box has swapped, it stays high for the rest of its uptime whatever the
# machine is doing now.  So a box that swapped once had A17 closed all day.
#
# Measured on this box while writing the fix — every number at the same moment:
#
#   vm.swapusage used ......... 8630M of 10240M = 84.3%   -> REFUSED at the 50% line
#   memory_pressure ........... 52% system-wide FREE      -> 48% in use, permits
#   kern.memorystatus_vm_pressure_level ... 1 (normal)
#   load ...................... 3.5 against a line of 10
#
# ~30 consecutive refusals across one session, every lane forced into
# one-shot-compile, and three red tenures that a 15-second scratch check would
# have caught — each paying a ~2000s queue cycle instead.  ALL OF IT AN
# INSTRUMENT ARTIFACT.
#
# THE LINE IS NOT THE PROBLEM AND IS NOT MOVED.  50% stays exactly where it
# was; what changes is that the number fed to it is a CURRENT-STATE reading on
# both platforms.  Linux's /proc/meminfo SwapFree was already current-state and
# is untouched.
#
# > A refusal is only as good as the quantity it refuses on, and a high-water
# > mark is a record of the past wearing the units of the present.
#
# AND THE NUMBER MUST NAME ITS INSTRUMENT.  "swap 88.5%" was believable
# precisely because it was unlabelled — it read as a pressure reading and was
# a uptime-long memory of one bad minute.  Every line below carries the
# instrument and the platform, so the next person to doubt it can check the
# same source in one command.
# THE KERNEL'S OWN SURVIVABILITY VERDICT, as a first-class reading.
#
# It exists inside `read_pressure` as a FALLBACK, which is the wrong shape for
# the acquire gate: there the question is not "how much memory is in use" but
# "is the thing that reclaims and kills already under pressure", and the kernel
# is the only instrument that answers it directly.
#
#   1 normal | 2 warn | 4 critical
#
# Reported with its transform, like every other line: the number alone has been
# misread twice in this repository.
read_pressure_level() {         # -> "<level> <instrument>"
  [ -n "${LS_MOCK_PRESSURE_LEVEL_FULL:-}" ] && { printf '%s\n' "$LS_MOCK_PRESSURE_LEVEL_FULL"; return 0; }
  local lvl
  lvl="${LS_MOCK_PRESSURE_LEVEL:-$(sysctl -n kern.memorystatus_vm_pressure_level 2>/dev/null || true)}"
  case "$lvl" in
    1) printf '1 memorystatus_vm_pressure_level=1-normal(macos)\n' ;;
    2) printf '2 memorystatus_vm_pressure_level=2-warn(macos)\n' ;;
    4) printf '4 memorystatus_vm_pressure_level=4-critical(macos)\n' ;;
    *) printf 'unknown memorystatus_vm_pressure_level=unavailable\n' ;;
  esac
}

read_pressure() {               # -> "<pct-in-use> <instrument>"
  [ -n "${LS_MOCK_PRESSURE:-}" ] && { printf '%s\n' "$LS_MOCK_PRESSURE"; return 0; }
  local mi mp lvl free
  # LINUX: SwapTotal/SwapFree is a CURRENT-STATE reading and always was.
  mi="${LS_MOCK_MEMINFO:-/proc/meminfo}"
  if [ -r "$mi" ]; then
    awk '/^SwapTotal:/{t=$2} /^SwapFree:/{f=$2}
         END{ if (t+0 <= 0) printf "0 meminfo:no-swap\n"
              else printf "%.1f meminfo:SwapTotal-SwapFree(linux)\n", (t-f)*100/t }' "$mi"
    return 0
  fi
  # macOS: the free percentage is what `memory_pressure` calls system-wide
  # free, which is a reading of NOW.  In-use is its complement, so the same
  # 50% line means the same thing it always did.
  if [ -n "${LS_MOCK_MEMPRESSURE:-}" ]; then mp="$LS_MOCK_MEMPRESSURE"
  else mp="$(timeout 15 memory_pressure 2>/dev/null || true)"; fi
  free="$(printf '%s\n' "$mp" | awk '/System-wide memory free percentage/ {
            v = $NF; gsub(/[^0-9.]/, "", v); if (v != "") { print v; exit } }')"
  # THE LABEL NAMES THE TRANSFORM, not only the source.  `memory_pressure:free%`
  # labelled an IN-USE number with the name of its complement, and a reader
  # quoting it read the free figure as the pressure — from this line's own
  # output.  Naming the instrument was necessary and NOT SUFFICIENT: an
  # unlabelled POLARITY is the same defect one turn of the screw down.
  if [ -n "$free" ]; then
    awk -v f="$free" 'BEGIN{ printf "%.1f memory_pressure:100-free%%(macos)\n", 100 - f }'
    return 0
  fi
  # FALLBACK, still a pressure instrument: the kernel's own level.  Mapped onto
  # the same 0-100 scale so ONE line governs both platforms — 1 normal, 2 warn,
  # 4 critical.
  lvl="${LS_MOCK_PRESSURE_LEVEL:-$(sysctl -n kern.memorystatus_vm_pressure_level 2>/dev/null || true)}"
  case "$lvl" in
    1) printf '0 memorystatus_vm_pressure_level=1-normal(macos)\n'; return 0 ;;
    2) printf '75 memorystatus_vm_pressure_level=2-warn(macos)\n'; return 0 ;;
    4) printf '100 memorystatus_vm_pressure_level=4-critical(macos)\n'; return 0 ;;
  esac
  # ABSENCE IS NOT PRESSURE.  A courtesy line that blocks because it could not
  # measure is the defect this whole entry is about, one level down — so an
  # unreadable instrument permits and SAYS it permitted blind.
  printf '0 unavailable(no-instrument)\n'
}

over() {                        # over A B -> 0 when A > B, in floating point
  awk -v a="$1" -v b="$2" 'BEGIN { exit !(a+0 > b+0) }'
}
