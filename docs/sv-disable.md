# Disable statements — repricing boundary

IEEE §9.6.2 and §12.6 transfer control with `disable`: a named block or
statement label is terminated, its remaining statements are skipped, and
control resumes after the disabled scope. A disable can act as loop exit or
continue, and a named fork/block can cancel retained child activity.

## Why disable remains a boundary

The envelope has no named-scope identity, cancellation token or retained
continuation tree. Treating disable as an ordinary `break`, returning from the
current process, or ignoring it changes nested-block and fork lifetimes.
Escaped labels and statement labels also use separate source binding rules.

The public tier therefore keeps every `DisableStatement` loud. No target is
guessed, no child or wait is silently canceled, and no second scheduler is
introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `DisableStatement` in **45** files:
**28** are disable-only and **17** co-occurring. Repricing the sole files finds
**28** spans: **25** named targets, **2** escaped targets and **1** statement
label. Reproduce the table with:

```text
python3.9 extractors/sv/disable_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and does not cancel a process or block.
