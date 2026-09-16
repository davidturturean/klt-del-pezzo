# KLT del Pezzo surfaces

**Singular points of klt del Pezzo surfaces of Picard number one in positive characteristic**

This repository contains a 40-page mathematical manuscript and an ongoing Lean 4 formalization. The manuscript presents a proof of the bound of seven distinct singular points for normal projective klt surfaces with ample Q-Cartier anticanonical divisor and Picard number one over an algebraically closed field of characteristic greater than two. It also develops Frobenius constructions related to the examples of Bernasconi and Keel–McKernan.

**The full seven-point theorem and the complete example constructions remain open in Lean.** The accepted checkpoint includes substantial geometry on actual schemes, divisors and line bundles, together with finite graph and lattice arguments. Four named manuscript results have passed individual acceptance checks.

[Read the paper](source/manuscript.pdf) · [Formalization guide](notes/FORMALIZATION_GUIDE.md) · [Paper-to-Lean map](notes/PAPER_TO_LEAN.md) · [Trust and assumptions](notes/TRUST.md) · [Reproduce the snapshot](notes/REPRODUCIBILITY.md)

## Mathematical development

The accepted work includes the Picard group of a rational tree, Stieltjes inverse positivity, rooted-tree inverse formulas and the ten-forest classification. The geometry library develops Cartier and Weil divisors, Picard and numerical classes, intersection pairings, sheaf cohomology, ampleness, and explicit Frobenius blowup charts. Each theorem retains its field, regularity, projectivity and source hypotheses.

The remaining work includes the global surface-theory inputs and geometric constructions needed to connect these results to the singular-point bound. The finite forest classification applies to abstract weighted graphs; the geometric reduction must supply its hypotheses. See the [remaining obligations](notes/STATUS.md#remaining-obligations).

## Accepted checkpoint

This package records **candidate1559**, accepted on 13 September 2026, from source commit `8b6110c192269d3c3b2d80c2e54bef9f25864865`.

| Recorded item | Checkpoint |
| --- | --- |
| Lean / Mathlib | Lean 4.19.0 / `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| Mathematical modules | 1,559 |
| Mathematical declarations | 28,595 |
| Named manuscript results accepted | 4 of 47 |
| Support obligations accepted in their recorded scope | 32 of 72 |
| Approved literature assumptions | 4 exact Stacks Project statements |

These inventory counts do not measure a percentage of proof completion. Three accepted support entries are attribution or context records with no Lean declarations. Many other support entries establish arithmetic clauses while their geometric applications remain open.

The archived dependency audit reports zero failed declarations within its stated policy. It checks the exact source snapshot and permitted dependencies; manuscript fidelity and geometric scope are separate reviews. The package includes the certificate, its source hashes and the [accepted scope](notes/STATUS.md).

## Repository contents

| Path | Contents |
| --- | --- |
| [`source/`](source/README.md) | Frozen manuscript PDF and LaTeX source |
| [`KltDP/`](KltDP) | Production Lean sources |
| [`KltDP/Manuscript/`](KltDP/Manuscript) | Wrappers corresponding to manuscript statements |
| [`notes/`](notes/FORMALIZATION_GUIDE.md) | Reading guide, claim map, scope and reproduction |
| [`audit/`](audit/README.md) | Source-bound checkpoint, compressed certificate and claim records |
| [`scripts/verify_package.py`](scripts/verify_package.py) | Lightweight integrity and claim-link checks |

## Verification

```sh
python3 scripts/verify_package.py
```

This command checks packaged hashes, Lean import closure, toolchain pins and the correspondence between accepted declaration names and the archived certificate. It does not execute Lean. Compilation instructions and the distinction between a fresh build and the recorded certificate are in [REPRODUCIBILITY.md](notes/REPRODUCIBILITY.md).

For source attribution, citation and reuse, see [CITATION.md](CITATION.md) and [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
