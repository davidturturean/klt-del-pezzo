# Checkpoint evidence

The package contains selected evidence for accepted checkpoint **candidate1559**.

| Artifact | Purpose |
| --- | --- |
| [snapshot.json](snapshot.json) | Checkpoint identifiers, counts, manuscript hashes and retained build IDs |
| [claim-status.json](claim-status.json) | All 119 result/support rows, accepted declarations, conditional scopes and source-record hashes |
| [literature-assumptions.json](literature-assumptions.json) | Exact four admitted literature declarations and frozen source/type hashes |
| [production-v4-candidate1559-20260913.json](checkpoints/production-v4-candidate1559-20260913.json) | Original source-bound checkpoint |
| [production_v4_candidate1559_validation.json.gz](production_v4_candidate1559_validation.json.gz) | Original dependency-policy certificate, compressed without content changes |
| [candidate1559_root_acceptance.json](candidate1559_root_acceptance.json) | Original compiled-checkpoint acceptance and semantic scope |
| [CompiledTrust.lean](CompiledTrust.lean) | Original driver for emitting the compiled-environment trust report |

The checkpoint and acceptance records retain references to historical artifacts outside this distribution. They remain archival provenance references. Routine logs, full object files, private workspaces, source experiments and the multi-gigabyte raw inventory are excluded. [REPRODUCIBILITY.md](../notes/REPRODUCIBILITY.md) describes what can be checked from this package and what a fresh build requires.
