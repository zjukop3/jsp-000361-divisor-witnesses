# Erdős Problem 444 — divisor witnesses

This repository contains a complete Lean proof of Erdős Problem 444 and a
new interface exposing explicit witnesses.  The original theorem is
`Erdos444.erdos_444` in [ErdosProblems/Erdos444.lean](ErdosProblems/Erdos444.lean).
The formal statement uses the literal half-open real cutoff and `EReal` limsup,
so it covers every infinite `A ⊆ ℕ` and every natural exponent `k`.

The source is pinned to Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.  Build it with:

```text
lake build DivisorWitnesses
lake env lean Audit.lean > axiom-audit.log
python3 scripts/check_axioms.py axiom-audit.log
lake env leanchecker --fresh --verbose DivisorWitnesses
python3 scripts/check_sources.py
```

`DivisorWitnesses.pointwise_large_value` turns the tail-unbounded quotient into
an actual integer `n` above any requested cutoff.  `diagonal` recursively picks
strictly increasing such witnesses.  `diagonal_tendsto` proves that one common
sequence works for every real exponent `r`, including negative exponents, after
normalizing by `(1 + reciprocalMass)^r`.  `infinite_iff_diagonal` records the
converse finite-set obstruction.

The complete original formalization and its mathematical proof were already
published by plby.  This repository does not claim first discovery or first
formalization.  The imported source is pinned at
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`; the provenance manifest records
each imported file and SHA-256.  Three small finite interfaces are attributed
excerpts, and their original surrounding analytic modules are not imported.
The pinned `PrimeMertens` dependency comes from FormalPantheon commit
`ffbb65c21afc8a36ace67720f1b0df1c63d26bd1`.  See `upstream-manifest.json` and
the notices in the Lean files for exact attribution.  The new statements and
adaptations were prepared by zjukop3 with OpenAI ChatGPT/Codex assistance.

The prize repository should receive only the catalog reference, never this
source tree or its build artifacts.
