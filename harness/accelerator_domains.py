#!/usr/bin/env python3
"""Check that accelerator evidence declares an actual admission domain."""

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
PATH = ROOT / "extractors" / "python" / "extract.py"


def load_extractor():
    spec = importlib.util.spec_from_file_location("approved_python_extractor", PATH)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    registry = load_extractor().ACCELERATOR_ADMISSIONS
    errors = []
    for name, record in sorted(registry.items()):
        if not record.get("evidence"):
            errors.append("%s has no evidence" % name)
        if not record.get("equivalent") and record.get("domain_admitted"):
            errors.append("%s claims an admission domain despite divergence" % name)
        if record.get("equivalent") and not record.get("domain_admitted"):
            errors.append("%s is equivalent but has no admission domain" % name)
    if errors:
        raise SystemExit("accelerator_domains: " + "; ".join(errors))
    print("accelerator_domains: %d registry entries have explicit domains" % len(registry))


if __name__ == "__main__":
    main()
