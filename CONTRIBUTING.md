# Contributions

Contributions should state the exact mathematical claim and preserve its original geometric objects and hypotheses. A new source module, a successful build and acceptance of a manuscript result are separate steps.

Before developing a substantial foundation, check the pinned Mathlib, newer Mathlib and relevant Lean libraries for a compatible proof or a bounded port. Preserve upstream licenses and provenance when porting code. Keep the current pins unless a migration is explicitly reviewed.

Proofs must not use `sorry`, `admit`, native evaluator proof axioms, unchecked oracles or additional unapproved assumptions. Proposed literature inputs require an exact published statement, a faithful Lean translation, a type/source audit and separately proved specializations. The approved list is in [TRUST.md](notes/TRUST.md).

Each change should identify the affected manuscript/support IDs, provide the source correspondence and full hypothesis list, and record the exact build and dependency evidence. A source or arithmetic result should retain its conditional status until the geometric hypotheses are supplied. Unimplemented endpoints belong in the claim inventory rather than in unfinished production proof terms.

The [reproduction guide](notes/REPRODUCIBILITY.md) describes compilation on an isolated build server and the evidence required for a new certificate. Lightweight package checks can be run with `make verify`.
