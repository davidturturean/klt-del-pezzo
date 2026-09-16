# Reproducibility

The package preserves the accepted source snapshot from commit `8b6110c192269d3c3b2d80c2e54bef9f25864865`. Every Lean source, the root import file, the toolchain files and the manuscript are copied without mathematical or editorial changes. [PROVENANCE.json](../PROVENANCE.json) records their hashes and any compression applied to evidence.

## Lightweight verification

Python 3.10 or later is sufficient:

```sh
python3 scripts/verify_package.py
```

The verifier checks the package checksum list, all 1,561 source bindings in the accepted checkpoint (1,559 mathematical modules, the auditor and root), local import closure, the Lean/Mathlib pins, the four literature-source hashes, all 119 claim rows and the accepted declarations against the original certificate. It prints a JSON report and returns a nonzero exit status on failure. These are source and record checks.

To inspect the unchanged certificate:

```sh
gzip -dc audit/production_v4_candidate1559_validation.json.gz > /tmp/klt-candidate1559-certificate.json
```

## Compilation

The project pins Lean `leanprover/lean4:v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, including transitive revisions in `lake-manifest.json`. The included certificate records a successful build and audit of the exact snapshot on 13 September 2026.

For an independent reproduction, use an isolated build server with the pinned `elan` toolchain and sufficient memory. The logical commands are:

```sh
lake exe cache get
lake build KltDP
lake env lean audit/CompiledTrust.lean > compiled-trust.log 2>&1
```

These commands are documented for the build environment; `make verify` does not invoke them. The recorded run used 4 CPUs, 26 GiB memory and no swap. The full trust report is large and the audit can take hours. A successful library build establishes compilation; the complete audit output and source binding are needed for a fresh dependency-policy certificate.

The original [`parse_compiled_audit256cpu4.py`](../scripts/parse_compiled_audit256cpu4.py) validates the project's archived runner records. It expects their exact before/after source manifests, dependency pins, command exits, resource observations and object/type manifests, plus the original literature-admission evidence. The small public package is sufficient to build the sources and emit a new report, but it is **not a complete byte-for-byte replay archive for the original runner parser**. No fresh full certification is claimed here.

## Retained build evidence

| Phase | Build ID |
| --- | --- |
| Library | `20260913T074624Z-955650` |
| Compiled dependency audit | `20260913T082256Z-967055` |
| Certificate parser | `20260913T124743Z-1019344` |

The archived certificate, [checkpoint](../audit/checkpoints/production-v4-candidate1559-20260913.json) and [acceptance receipt](../audit/candidate1559_root_acceptance.json) are included. Historical absolute paths in these records identify the original build environment; they are not installation paths or credentials. The 4,035,652,115-byte full inventory and routine build logs are excluded; their recorded hashes remain available in [snapshot.json](../audit/snapshot.json). Compiled `.olean` objects are not distributed in this package.

## Manuscript

The committed [PDF](../source/manuscript.pdf) has 40 pages. The [TeX source](../source/manuscript.tex) contains its bibliography and requires a standard LaTeX installation with the listed packages.

```sh
mkdir -p build/paper
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build/paper source/manuscript.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build/paper source/manuscript.tex
```

PDF timestamps can change on regeneration. The frozen PDF is retained unchanged; its rendering was inspected during packaging. A successful TeX build checks document production, not mathematical correctness.
