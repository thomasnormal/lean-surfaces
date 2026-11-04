# System-call format boundary — retained macro and output formatting

`SysCall:format` marks a system call whose format or argument text is outside
the admitted call representation. Sole rows include macro definitions with
default or empty arguments and one runtime `$display` call.

## Why format calls remain loud

IEEE 1800-2023 §§20.2 and 22.5.1 distinguish macro argument substitution from
runtime system-task formatting. Empty macro actuals, trailing defaults and
commas are processed before the runtime call exists; `$display` output also
depends on scheduler ordering. The envelope has no macro-expansion trace or
format-argument model. No macro is expanded by guesswork and no output is
reordered through a second scheduler.

## 2026-10-22 census and decision

The fresh 22,043-path census records `SysCall:format` in **6** files: **5** are
sole refusals and one co-occurs. Re-elaborating the sole files finds **5**
format spans: four macro-expansion/default-argument cases and one runtime
display format. The runtime-display label overlaps macro definitions that
contain `$display`. Reproduce with:

```text
python3.9 extractors/sv/syscall_format_reprice.py --corpus /path/to/sv-tests-2/tests
```

The instrument reports source shapes only; it does not expand macros or emit
output.
