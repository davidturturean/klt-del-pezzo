# Singular points of klt del Pezzo surfaces of Picard number one in positive characteristic

> David Turturean, `davidct@mit.edu`

[![Build Lean formalization](https://github.com/davidturturean/klt-del-pezzo/actions/workflows/build-lean.yml/badge.svg)](https://github.com/davidturturean/klt-del-pezzo/actions/workflows/build-lean.yml)
[![Lean 4.19.0](https://img.shields.io/badge/Lean-4.19.0-blue)](lean-toolchain)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

This repository contains the paper and a complete Lean 4 formalization of the uniform seven-point bound for rank-one klt del Pezzo surfaces in characteristic greater than two, together with the examples showing that the bound is sharp in characteristic three and false in characteristic two.

## Result

Let $k$ be an algebraically closed field of characteristic $p > 2$ and let $X$ be a projective surface over $k$ with klt singularities, $\rho(X) = 1$ and $-K_X$ ample. Then $X$ has at most seven singular points.

Over every algebraically closed field of characteristic three there is such a surface with exactly seven singular points and $K_X^2 = 1/3$; over every algebraically closed field of characteristic two there are such surfaces with $2n+1$ singular points for every $n \ge 3$.

The public Lean declarations are

```lean
KltDP.Manuscript.uniformSevenPointBound
    (p : ℕ) [CharP k p] (hp : 2 < p) (X : NormalProjectiveSurface k)
    (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1) :
    X.singularPoints.card ≤ 7

KltDP.Manuscript.S01.sharpnessExampleCharThree
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k 3] :
    ∃ X : NormalProjectiveSurface k, IsKltDelPezzo X ∧ X.picardRank = 1 ∧
      X.singularPoints.card = 7 ∧ ∃ R : ResolutionDatum k, R.X = X ∧ R.Lsq = 1 / 3

KltDP.Manuscript.S01.characteristicTwoFamily
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2] (n : ℕ) (hn : 3 ≤ n) :
    ∃ X : NormalProjectiveSurface k, IsKltDelPezzo X ∧ X.picardRank = 1 ∧
      X.singularPoints.card = 2 * n + 1 ∧
      ∃ R : ResolutionDatum k, R.X = X ∧ R.Lsq = 2 / ((n : ℚ) - 2)
```

in [`KltDP/Manuscript/Main/Final.lean`](KltDP/Manuscript/Main/Final.lean) and [`KltDP/Manuscript/S01/Examples.lean`](KltDP/Manuscript/S01/Examples.lean). `NormalProjectiveSurface k` is an actual normal projective surface over `k` (a scheme), `IsKltDelPezzo` is the klt and ample-anticanonical condition, and `X.singularPoints` is the finite set of non-regular points. Every one of the paper's 47 numbered statements has a Lean counterpart; the map is in [`notes/PAPER_TO_LEAN.md`](notes/PAPER_TO_LEAN.md).

## Repository contents

```text
.
├── KltDP.lean                       # Lean root importing the complete library
├── KltDP/                           # 3,525 modules, about 435,000 lines
│   ├── Manuscript/                  # the paper, section by section
│   │   ├── Main/Final.lean          # Theorem 1.1
│   │   ├── S01/Examples.lean        # Theorem 1.2
│   │   ├── S02 … S11/               # Lemmas 2.1 to A.3
│   │   └── Datum/                   # the resolution datum (S, D, L) of the paper
│   ├── Geometry/                    # schemes, divisors, intersection theory, cohomology, blowups, cones
│   ├── Examples/                    # the Frobenius constructions of Section 10
│   ├── LinearAlgebra/, Lattices/, Codes/, Support/   # the finite arguments
│   ├── CommutativeAlgebra/, RingTheory/, Topology/, CategoryTheory/, Combinatorics/, AdmissionProbe/
│   ├── Literature/                  # the 28 admitted published statements (one axiom each)
│   ├── Compatibility/               # ports of existing Lean libraries to the pinned toolchain
│   └── Audit/Trust.lean             # the compiled dependency audit
├── source/                          # manuscript.pdf, manuscript.tex
├── notes/                           # AXIOMS.md, PAPER_TO_LEAN.md, REPRODUCIBILITY.md
├── audit/                           # axiom report, source audits, claim records, checkpoints/ (history)
├── scripts/, Makefile               # verification commands
├── .github/workflows/build-lean.yml # package checks and the full build
├── lakefile.toml, lake-manifest.json, lean-toolchain
├── PROVENANCE.json, SHA256SUMS      # copy manifest and checksums of every packaged file
├── problem_statement.md, CITATION.cff, NOTICE, LICENSE, CONTRIBUTING.md
└── THIRD_PARTY_NOTICES.md, LICENSES/, docs/   # third-party notices and retained license texts
```

## Build and verify

Install [`elan`](https://github.com/leanprover/elan), then run:

```bash
lake exe cache get
make check
```

The individual commands are:

```bash
make imports   # all project-local imports resolve
make audit     # no sorry/admit, no native evaluator, axioms only in KltDP/Literature
make verify    # package checksums and records
make build     # compile the library
make axioms    # print and check the final theorems' kernel dependencies
```

Lean and Mathlib are pinned to `v4.19.0` and `c44e0c8ee63ca166450922a373c7409c5d26b00b`, including transitive revisions in `lake-manifest.json`. A full build takes several hours; the workflow runs it on the project's build VM on every push, and its `#print axioms` output is checked against the list below.

## Axioms used

The formalization has no `sorry`. The final theorems depend on `propext`, `Classical.choice`, `Quot.sound` and the following 28 published statements, each admitted as a single `axiom` in `KltDP/Literature/` in the exact form used, with its source recorded in the file. Full statements, Lean signatures and specialisations are in [`notes/AXIOMS.md`](notes/AXIOMS.md).

| Lean declaration (`KltDP.Literature.…`) | Source | Statement |
|---|---|---|
| `Hartshorne.castelnuovo_contraction_literal` | Hartshorne, *Algebraic Geometry*, V.5.7 (p. 414) | A (−1)-curve E ≅ P¹ on a regular projective surface is the exceptional curve of a point blowup: S is the blowup of a regular projective surface T at a point, with E the fibre. |
| `Hartshorne.hasContractionLifts_instance` | Hartshorne V.3.6, II.7.15, II.7.13(a)/II.7.14, V.5.3/V.5.7; multiplicity def. V.3 p. 388 | Strict transforms exist along any contraction of a (−1)-curve between regular projective surfaces: b\*Q = Q̃ + m·E, m = 0 iff Q misses the centre, Q̃ ≅ Q when m ≤ 1, every curve ≠ E is a strict transform. |
| `Hartshorne.hurwitz_degreeTwo_projectiveLine_instance` | Hartshorne IV Cor. 2.4 (Hurwitz) + Prop. IV.2.2(b); also Stacks 0C1B | A degree-two map B → P¹ from a curve B ≅ P¹ in char p > 2 has at most two totally ramified points (points of P¹ with a singleton fibre). |
| `Hartshorne.integral_numerical_group_free_finite_literal` | Hartshorne V Remark 1.9.1, p. 364 | Weil divisors modulo numerical equivalence on a regular integral projective surface form a free abelian group of finite rank. |
| `Hartshorne.minimal_surface_classification_literal` | Hartshorne V.6.1 | For a minimal regular projective surface with canonical divisor K: all plurigenera vanish iff P₁₂ = 0, and P₁₂ = 0 iff X is birational to P² or X is ruled over a regular curve (P¹-bundle with a section). |
| `Hartshorne.nonsingular_complete_surface_projective_literal` | Hartshorne II Remark 4.10.2(b), p. 105 (defs. pp. 105, 32/130, 103) | Every nonsingular complete surface over an algebraically closed field is projective (closed immersion into some Pⁿ). |
| `Hartshorne.point_blowup_structure_cohomology_literal` | Hartshorne V.3.4, pp. 387–388 (conventions pp. 357/386) | For the blowup π of a regular projective surface at a closed point: π\*O = O, Rⁱπ\*O = 0 for i > 0, and Hⁱ(X̃, O) ≅ Hⁱ(X, O) for all i. |
| `Hartshorne.ruled_surface_genus_literal` | Hartshorne V.2.5 | For a surface ruled over a curve of genus g: χ(O_X) − 1 = −g, H⁰(ω_X) = 0, h¹(O_X) = g. |
| `Hartshorne.ruled_surface_picard_literal` | Hartshorne V.2.3 | For a surface ruled over C with section S₀ and fibre F: Pic X ≅ ℤ ⊕ Pic C, Num X ≅ ℤ² on the classes of S₀, F, with S₀·F = 1 and F² = 0. |
| `Hartshorne.surface_hodge_index_literal` | Hartshorne V Theorem 1.9, p. 364 | Hodge index: H ample, D ≢ 0 numerically, D·H = 0 ⇒ D² < 0. |
| `Hartshorne.surface_nakai_moishezon_literal` | Hartshorne V Theorem 1.10, p. 365 | Nakai–Moishezon: D is ample iff D² > 0 and D·C > 0 for every irreducible curve C. |
| `Hartshorne.surface_riemannRoch_literal` | Hartshorne V Theorem 1.6, p. 362 | Riemann–Roch for surfaces: h⁰(D) − h¹(D) + h⁰(K − D) equals the Riemann–Roch number of D (½·D·(D − K) + 1 + p_a, as encoded by `rrNumber`). |
| `Stacks.affine_morphism_cohomology_literal` | Stacks 089W, Lemma 30.2.4, rev. 540451b3 | For an affine morphism f and quasi-coherent M, Hⁿ(Y, f\*M) ≅ Hⁿ(X, M), naturally in M. |
| `Stacks.blowupRegularPoint_literal` | Stacks 0AGQ (Lemma 54.3.1, quoted) / 0AGR / 0C5P; Hartshorne V.3.1 | The exceptional fibre of the blowup of a regular projective surface at a closed point is P¹ over k and its conormal sheaf has degree 1 (E ≅ P¹, E² = −1). |
| `Stacks.closed_point_blowups_dominate_proper_literal` | Stacks 0AHI, resolve.tex 928–941, commit a04446e5 | A proper morphism to a Noetherian scheme that is an isomorphism away from finitely many regular 2-dimensional closed points is dominated by a finite sequence of point blowups over those points. |
| `Stacks.field_isJ2` | Stacks 07PJ item (1), commit 540451b3; defs 07P7, 00KU | Every field is J-2: every finite-type algebra over a field has open regular locus. |
| `Stacks.properCohomology_finite` | Stacks 02O6, rev. 540451b3 | Cohomology of a coherent sheaf on a scheme proper over a Noetherian ring A is a finitely generated A-module in every degree. |
| `Stacks.properFlat_fiberEuler_literal` | Stacks Lemma 36.32.2, Tag 0B9T, rev. 540451b3, perfect.tex 7960–7983 | For a proper finitely presented morphism and a finitely presented module flat over the base, the fibrewise Euler characteristic is locally constant and commutes with base change. |
| `Stacks.proper_curve_pullback_degree_literal` | Stacks 0AYZ (with 0AYR, 02NY) | For a nonconstant map f : C → D of integral proper curves and locally free E of rank n on D, deg f\*E = [K(C):K(D)]·deg E (Euler-characteristic degrees). |
| `Stacks.proper_curve_tensor_degree_literal` | Stacks Lemma 33.44.7, tag 0AYX; Def. 33.44.1, tag 0AYR; varieties.tex rev. 540451b3, lines 9475–9488, 9717–9733 | On a proper scheme of dimension ≤ 1 over a field, deg(E ⊗ V) = n·deg V + m·deg E for locally free E, V of ranks n, m. |
| `Stacks.regularLocal_isUFD` | Stacks 0AG0, rev. 540451b3; 034S (domain), 00KU (regular local) | A regular local ring is a domain and a unique factorisation domain. |
| `Stacks.regular_smooth_loci_perfect_literal` | Stacks 0B8X, Lemma 33.25.8, rev. a04446e5 | For a reduced scheme locally of finite type over a perfect field, the smooth locus equals the regular locus and is open and dense. |
| `Stacks.smooth_standardSmooth_cover_literal` | Stacks 00TA, first cover assertion of Lemma 10.137.9, rev. a04446e5 | A smooth ring map R → S admits a cover by principal localisations S_g on which R → S_g is standard smooth. |
| `Stacks.steinFactorization_noetherian_literal` | Stacks 03H0 with relative normalisation as in 035H, rev. 540451b3 | Stein factorisation: a proper morphism to a locally Noetherian scheme factors as a proper morphism with geometrically connected fibres and O_T = f'\*O_X followed by a finite morphism; T is the relative Spec of f\*O_X and the relative normalisation. |
| `Stacks.lipman_resolution_of_normal_completions_literal` | Stacks 0BGP, Theorem 54.14.5, (4) ⇒ (2) | An integral Noetherian surface whose normalisation is finite, has finitely many non-regular points, and has normal completed local rings there, admits a proper birational morphism from a regular integral locally Noetherian scheme (a resolution). |
| `Keel.semiampleness_completeSystem_literal` | Keel, Ann. Math. 149 (1999) 253–286, Theorem 0.2, p. 254; defs 0.0–0.1 pp. 253–254; conventions p. 259 | In characteristic p > 0, a nef line bundle on a projective scheme is semiample iff its restriction to the exceptional locus is semiample. |
| `Zariski.closedPoint_normal_completion_literal` | Zariski, Ann. Inst. Fourier 2 (1950), Theorem 2, p. 162 | At a closed point of an integral affine variety over a field where the local ring is integrally closed, the maximal-ideal completion is a local integrally closed domain. |
| `Tanaka.contraction_44_instance` | Tanaka, *Minimal model program for excellent surfaces*, AIF 68 (2018) no. 1, 345–376, Theorem 4.4, p. 365 | A K_S-negative extremal ray of the closed cone of curves of a regular projective surface over an algebraically closed field is contracted by a morphism to a projective scheme Y with f\*O_S = O_Y, contracting exactly the curves in the ray, and ρ(Y) = ρ(S) − 1. |

```bash
./scripts/print_axioms.sh
```

reports exactly these names (the recorded output is [`audit/axiom-report.txt`](audit/axiom-report.txt)).

## Citation

```bibtex
@misc{turturean2026kltdelpezzo,
  author       = {David Turturean},
  title        = {Singular points of klt del Pezzo surfaces of Picard number one in positive characteristic},
  year         = {2026},
  howpublished = {GitHub repository},
  url          = {https://github.com/davidturturean/klt-del-pezzo}
}
```

See [`CITATION.cff`](CITATION.cff) for machine-readable metadata.

## License and disclosure

The Lean code and repository documentation are licensed under Apache-2.0. The paper remains copyright David Turturean. The manuscript's proof was produced by GPT-6-Astra Pro, starting from a significantly longer, enumerative manuscript generated by GPT-5.6-Pro. The Lean formalization used Codex (gpt-6-astra) for the foundational library and Claude Fable 5.1 in Claude Code for the modules that carry the manuscript's argument to the main theorem. David Turturean is responsible for the final mathematical claims and exposition. Ported files retain their original notices; see [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md), [`NOTICE`](NOTICE) and [`LICENSE`](LICENSE).
