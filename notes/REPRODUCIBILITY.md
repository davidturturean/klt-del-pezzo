# Reproducibility

The project pins Lean `leanprover/lean4:v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, including transitive revisions in `lake-manifest.json`.

## Build

```sh
lake exe cache get        # Mathlib oleans
lake build KltDP          # the whole library, 3,525 modules
./scripts/print_axioms.sh # #print axioms of the main theorem and the two examples
```

The last command re-elaborates `KltDP/Manuscript/Main/Final.lean` and prints the dependency lists; `python3 scripts/check_axioms.py audit/axiom-report.txt` checks them against the allowlist in `notes/AXIOMS.md`. `make check` runs the import, placeholder, checksum, build and axiom steps in order.

A full build takes several hours on a multi-core machine after the Mathlib cache is fetched. The GitHub Actions workflow runs the full build on the project's build VM on every push to `main`; the lightweight package checks run on a hosted runner.

## Recorded evidence

| Record | Location |
| --- | --- |
| `#print axioms` of the final theorems | `audit/axiom-report.txt` |
| Compiled dependency audit of the full snapshot (policy v7) | `audit/checkpoints/final-2026-09/` |
| Historical audit of the 1,559-module checkpoint of 13 September 2026 (policy v6, four Stacks axioms) | `audit/checkpoints/candidate1559/` |

## Manuscript

```sh
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build/paper source/manuscript.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build/paper source/manuscript.tex
```

The committed `source/manuscript.pdf` is the frozen 40-page version (SHA-256 in `source/README.md`).
