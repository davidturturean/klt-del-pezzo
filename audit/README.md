# Audit records

| Record | Purpose |
| --- | --- |
| [axiom-report.txt](axiom-report.txt) | Verbatim `#print axioms` output of the main theorem `KltDP.Manuscript.uniformSevenPointBound` from the build VM; checked by `scripts/check_axioms.py` against the trust boundary |
| [source-audit.json](source-audit.json) | Comment-aware placeholder scan of every Lean source (`scripts/check_no_placeholders.py`): no `sorry`/`admit`, no native evaluator, no `constant`, `axiom` only in the 28 allowlisted literature modules |
| [source-lint-summary.json](source-lint-summary.json) | Summary of the trust-boundary source lint (`scripts/audit_sources.py`) over the complete tree; every reported token is classified in its note |
| [literature-assumptions.json](literature-assumptions.json) | The 28 admitted literature statements: declaration names, modules, source hashes and, where recorded, the pinned published source |
| [claim-status.json](claim-status.json) | All 119 result/support rows with their compiled declarations, scope notes and isolated clauses; rendered as [PAPER_TO_LEAN.md](../notes/PAPER_TO_LEAN.md) |
| [third-party-sources.json](third-party-sources.json) | Source-header inventory of ported files (see [THIRD_PARTY_NOTICES.md](../THIRD_PARTY_NOTICES.md)) |
| [CompiledTrust.lean](CompiledTrust.lean) | Driver for emitting the compiled-environment trust report (`KltDP.Audit.Trust`) |
| [checkpoints/final-2026-09/](checkpoints/final-2026-09/) | Compiled dependency audit of this snapshot (policy v7, 2026-09-18): compressed certificate, trust summary, `#print axioms` probe output, runner records and logs; see [docs/TRUST_AUDIT_V7.md](../docs/TRUST_AUDIT_V7.md) |
| [checkpoints/candidate1559/](checkpoints/candidate1559/) | History: the 1,559-module checkpoint of 13 September 2026 (four Stacks axioms): [snapshot](checkpoints/candidate1559/snapshot.json), [checkpoint](checkpoints/candidate1559/production-v4-candidate1559-20260913.json), [acceptance](checkpoints/candidate1559/candidate1559_root_acceptance.json) and the compressed [certificate](checkpoints/candidate1559/production_v4_candidate1559_validation.json.gz) |

The historical records retain references to artifacts outside this distribution and to their original paths; they are archival provenance, not descriptions of the current tree. `python3 scripts/verify_package.py` checks the current records against the sources and the retained history without running Lean; [REPRODUCIBILITY.md](../notes/REPRODUCIBILITY.md) describes the build.
