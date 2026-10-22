# Symmetric wildcard case statements

The legacy self-check and timed surfaces admit unqualified integral
`casez` and `casex` statements (IEEE 1800-2023 §12.5.1).

`casez` ignores a bit position if either operand contains Z at that
position. The literal digit `?` is another spelling of Z. Every remaining
position must match exactly, including X against X. `casex` ignores X or Z
in either operand and compares the remaining known positions. The match
result is always definite. These rules apply to dynamic subject and item
values, including masks produced during simulation.

The frontend's whole-case width and signedness conversions apply before
matching. The extractor keeps those converted expressions and lowers the
statement to the same first-match `If` chain as ordinary `case`, with a
`CaseMatch` condition selecting the symmetric comparison. Comma-separated
labels retain source order. Default is the final fallback regardless of its
source placement; without a default, exhaustion executes nothing.

`LVec.matchesCase` shares one pure bit/list predicate between evaluation and
proofs. `SExpr.caseMatch` evaluates its operands and lifts that predicate to
a one-bit value. No operator spelling or scheduler rule is invented.
The existing statement stepper retains the selected body when it waits;
resumption does not rematch a changed subject. A later visit evaluates the
current values again.

Only supported pure integral operands are admitted. The purity check walks
the bound source before constant folding, so a folded call or increment
cannot erase an effect. Repeated pure subject reads in the `If` chain have
no intervening writes or waits. Unsupported storage and nonintegral operands
remain loud. `unique`, `unique0` and `priority` retain their diagnostic
obligations and remain loud, as do `case inside` and pattern cases on this
legacy path. See [unique case statements](sv-unique-cases.md) for the
`CaseStatement:Unique` boundary. Symbolic-mode wildcard statements and the M0
expression loader do not gain this SelfCheck expression. Invalid compilations retain the
existing case-lowering admission barrier.

The [fixtures](../Examples/system-verilog/wildcard_cases/README.md) compare
all 256 pairs of two-bit four-state values, signed/mixed/wide contexts,
dynamic masks, first/default/no-match behavior, nesting and selected bodies
across positive delays. Kernel theorems connect symmetric value matching,
expression evaluation and a selected delayed arm to the extracted source.
