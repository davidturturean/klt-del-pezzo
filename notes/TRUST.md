# Trust and literature assumptions

The accepted checkpoint uses ordinary Lean foundations (`propext`, `Classical.choice`, `Quot.sound`) and four explicitly admitted literature axioms. Each admission has a pinned Lean source and type, a pinned published source, and separately proved local adapters.

| Stacks tag | Assumed statement | Lean source |
| --- | --- | --- |
| [07PJ(1)](https://stacks.math.columbia.edu/tag/07PJ) | Fields are J-2 | [FieldJ2](../KltDP/Literature/Stacks/FieldJ2.lean) |
| [0AG0](https://stacks.math.columbia.edu/tag/0AG0) | A regular local ring is a unique factorization domain | [RegularLocalUFD](../KltDP/Literature/Stacks/RegularLocalUFD.lean) |
| [02O6](https://stacks.math.columbia.edu/tag/02O6) | Coherent cohomology of a scheme proper over a Noetherian affine base is finite over the original base ring | [ProperCohomologyFinite](../KltDP/Literature/Stacks/ProperCohomologyFinite.lean) |
| [0AYX](https://stacks.math.columbia.edu/tag/0AYX) | Tensor-degree formula for finite-rank locally free sheaves on a proper scheme of dimension at most one over a field | [CurveTensorDegreeLiteral](../KltDP/Literature/Stacks/CurveTensorDegreeLiteral.lean) |

The source pin for these entries is Stacks commit `540451b3e79a131df8eca4c4187448e49dcb262d`. The current web pages are reading links; [literature-assumptions.json](../audit/literature-assumptions.json) records the frozen declaration/type/source hashes.

The cohomology-finiteness input alone supplies no Riemann–Roch, duality or vanishing theorem. The tensor-degree input alone supplies no surface intersection pairing or Hodge theorem. The project proves separate constructions and adapters where available.

The accepted development now proves its affine-vanishing interface without adding a Stacks 01XB axiom. Keel, resolution, Riemann–Roch, duality and Hodge contracts remain unadmitted in this four-source checkpoint. For example, `SurfaceHodgeIndexSource.RawStatement` is a proposition passed explicitly to its conditional consumers. A definition of a proposition is not a proof of it.

## Recorded audit

The compressed [certificate](../audit/production_v4_candidate1559_validation.json.gz) is the original validator output. Its uncompressed SHA-256 is `a278eb3b98f42ed2280174a39040de1fa7f8f6008d46e02f6e5fdd837895f4b4`. It records 28,595 mathematical declarations, zero failed declarations, the permitted dependency sets, exact source hashes and native type references.

The certificate also retains compiler-generated unsafe implementation and runtime-companion records. Those are classified separately from logical roots; an occurrence in those diagnostic indexes does not by itself assert a mathematical axiom. The original auditor policy and parser are included for inspection.

Dependency validation does not assess manuscript completeness or statement fidelity. The [accepted checkpoint scope](STATUS.md), theorem signatures and [claim-level records](PAPER_TO_LEAN.md) provide those separate boundaries. The package verifier checks archive integrity and correspondence to the retained records. A fresh Lean build and mathematical review remain separate checks.
