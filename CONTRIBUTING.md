# Contributions

Contributions should state the exact mathematical claim and preserve its original geometric objects and hypotheses. A new source module, a successful build and the correspondence to a manuscript result are separate steps.

Before developing a substantial foundation, check the pinned Mathlib, newer Mathlib and relevant Lean libraries for a compatible proof or a bounded port. Preserve upstream licenses and provenance when porting code. Keep the current pins unless a migration is explicitly reviewed.

Proofs must not use `sorry`, `admit`, native evaluator proof axioms, unchecked oracles or additional unapproved assumptions. Proposed literature inputs require an exact published statement, a faithful Lean translation, a type/source audit and separately proved specializations. The admitted statements are listed in [notes/AXIOMS.md](notes/AXIOMS.md); `scripts/check_axioms.py` rejects any other dependency.

Each change should identify the affected manuscript IDs in [notes/PAPER_TO_LEAN.md](notes/PAPER_TO_LEAN.md), provide the source correspondence and full hypothesis list, and pass `make check` (imports, placeholder audit, package verifier, build and axiom report). The [reproduction guide](notes/REPRODUCIBILITY.md) describes the build and the recorded evidence.
