"""Reject unexpected foundations or missing theorem reports."""

import re
import sys
from pathlib import Path

expected = set(re.findall(r"#print axioms (\S+)", Path("Audit.lean").read_text()))
if not expected:
    raise SystemExit("No advertised results were found")
allowed = {"propext", "Classical.choice", "Quot.sound"}
log = Path(sys.argv[1]).read_text()
seen = set()
for name, raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
    axioms = {item.strip() for item in raw.split(",") if item.strip()}
    if axioms - allowed:
        raise SystemExit(f"Rejected axioms for {name}: {sorted(axioms - allowed)}")
    seen.add(name)
seen.update(re.findall(r"'([^']+)' does not depend on any axioms", log))
if missing := expected - seen:
    raise SystemExit(f"Missing reports: {sorted(missing)}")
print(f"PASS: {len(expected)} theorem reports use only allowed axioms.")
