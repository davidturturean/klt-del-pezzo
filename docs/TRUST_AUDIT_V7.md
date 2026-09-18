# Compiled trust audit, policy v7: twenty-eight literature admissions

This document records the delta from policy v6 (`lean419_logical_boundary_four_stacks_v6`, the
certificate of checkpoint candidate1559) to policy v7
(`lean419_logical_boundary_twentyeight_admissions_v7`), and the outcome of running the complete
pipeline on the final 3,525-module snapshot. `docs/TRUST_AUDIT.md` remains the description of the
auditor's mechanics; nothing below changes those mechanics.

## Summary

* The v6 four-axiom certificate covered a 1,559-module subset of the library.
* The full library (3,525 mathematical modules) uses **28 published inputs** as axioms. Policy v7
  versions the allowlist to exactly those 28 names, each bound to its owning module, source hash and
  type hashes by `audit/literature-assumptions.json`; nothing else in the policy is relaxed.
* The whole-library dependency policy is **not passed**: 12 modules contain custom elaborator code
  (`elab`), 9 of them with a source-level `partial def`; the 9 generated `_unsafe_rec` companions
  fail the unchanged root policy through their own partial safety. The trust report ends with
  `failed_declaration_count = 9`, status `dependency_policy_failed` and Lean exit
  status 1; the strict parser refuses a certificate (stage `parser_strict` below).
* The three logical roots `KltDP.Manuscript.uniformSevenPointBound`, `KltDP.Manuscript.S01.sharpnessExampleCharThree` and `KltDP.Manuscript.S01.characteristicTwoFamily` pass the policy with clean closures. Their
  transitive axioms are the three foundations and exactly the 28 admissions: the main theorem uses all
  28, each example uses 9. None of the 9 failures is reachable from any root along
  the auditor's exported dependency edges.
* 5 library modules are declaration-free (`KltDP.Geometry.AffineStalkCompletionExports`, `KltDP.Geometry.RegularProperCurveFieldIsoAudit`, `KltDP.Geometry.RuledSurfaceSourceGeometryAudit`, `KltDP.Geometry.SingularStalkCompletionNormalExports`, `KltDP.Geometry.SmoothPointBlowupAffineCanonicalCharts`): `#check`/`#print axioms`
  export files and an import followed by a docstring. They have no inventory rows and are itemized in
  the certificate under `declaration_free_modules` (section below).
* The source lint records 24 `elab`/`partial` findings in the 12 modules (and 168 review
  findings elsewhere); they are **reviewed and itemized, not discharged**: the lint status stays
  `source_lint_rejected`.
* The scoped parser mode `--itemize-nonroot-failures` emits a certificate with status
  `passed_with_itemized_nonroot_failures` under exactly the conditions listed below; it carries
  `dependency_policy_status: dependency_policy_failed` and lists every failure and finding.

## Why a new policy version

The v6 certificate (`audit/production_v4_candidate1559_validation.json`, 13 September 2026) covered
1,559 mathematical modules and an allowlist of exactly four Stacks Project literals:
`KltDP.Literature.Stacks.field_isJ2`, `regularLocal_isUFD`, `properCohomology_finite` and
`proper_curve_tensor_degree_literal`. Every other module of the library was kept out of the audited
root, so consumers of any other published statement never reached the auditor.

The complete library of 16 September 2026 depends on the three foundational axioms and on
twenty-eight published inputs (`manuscript_formalization_20260916/FINAL_AXIOMS.txt`). Under v6 every
consumer of the other twenty-four would be a forbidden transitive axiom. v7 versions the allowlist
honestly instead of excluding modules.

## The twenty-eight admissions

Canonical (lexicographic) name order, as emitted in `literature_axioms`:

| # | Axiom | Owning module | Published source |
| --- | --- | --- | --- |
| 1 | `KltDP.Literature.Hartshorne.castelnuovo_contraction_literal` | `KltDP.Literature.HartshorneCastelnuovoLiteral` | R. Hartshorne, Algebraic Geometry, GTM 52, Springer (1977); theorem Theorem V.5.7 (Castelnuovo's contraction criterion); page 414 |
| 2 | `KltDP.Literature.Hartshorne.hasContractionLifts_instance` | `KltDP.Literature.Hartshorne.StrictTransformInstance` | R. Hartshorne, Algebraic Geometry, GTM 52, Springer (1977); theorem Proposition V.3.6, Corollary II.7.15 and Proposition II.7.13, with Proposition V.5.3 (strict transforms under the contraction of a (-1)-curve), admitted as an instance |
| 3 | `KltDP.Literature.Hartshorne.hurwitz_degreeTwo_projectiveLine_instance` | `KltDP.Literature.Hartshorne.HurwitzDegreeTwoInstance` | R. Hartshorne, Algebraic Geometry, GTM 52, Springer (1977); theorem Corollary IV.2.4 (Hurwitz) and Proposition IV.2.2(b), degree-two P^1 -> P^1 instance in characteristic p > 2 |
| 4 | `KltDP.Literature.Hartshorne.integral_numerical_group_free_finite_literal` | `KltDP.Literature.Hartshorne.IntegralNumericalGroup` | R. Hartshorne, Algebraic Geometry, GTM 52, Springer (1977); theorem Chapter V, Remark 1.9.1; page 364; doi 10.1007/978-1-4757-3849-0 |
| 5 | `KltDP.Literature.Hartshorne.minimal_surface_classification_literal` | `KltDP.Literature.Hartshorne.MinimalSurfaceClassification` | R. Hartshorne, Algebraic Geometry, GTM 52, Springer (1977); theorem Theorem V.6.1 |
| 6 | `KltDP.Literature.Hartshorne.nonsingular_complete_surface_projective_literal` | `KltDP.Literature.Hartshorne.SurfaceProjectivity` | R. Hartshorne, Algebraic Geometry, GTM 52, Springer (1977); theorem Chapter II, Remark 4.10.2(b); page 105; doi 10.1007/978-1-4757-3849-0 |
| 7 | `KltDP.Literature.Hartshorne.point_blowup_structure_cohomology_literal` | `KltDP.Literature.Hartshorne.PointBlowupCohomology` | R. Hartshorne, Algebraic Geometry, GTM 52, Springer (1977); theorem Proposition V.3.4; page 387-388 |
| 8 | `KltDP.Literature.Hartshorne.ruled_surface_genus_literal` | `KltDP.Literature.Hartshorne.RuledSurfaceGenus` | R. Hartshorne, Algebraic Geometry, GTM 52, Springer (1977); theorem Corollary V.2.5 |
| 9 | `KltDP.Literature.Hartshorne.ruled_surface_picard_literal` | `KltDP.Literature.Hartshorne.RuledSurfacePicard` | R. Hartshorne, Algebraic Geometry, GTM 52, Springer (1977); theorem Proposition V.2.3 |
| 10 | `KltDP.Literature.Hartshorne.surface_hodge_index_literal` | `KltDP.Literature.Hartshorne.SurfaceHodgeIndex` | R. Hartshorne, Algebraic Geometry, GTM 52, Springer (1977); theorem Theorem V.1.9 (Hodge index theorem); page 364; doi 10.1007/978-1-4757-3849-0 |
| 11 | `KltDP.Literature.Hartshorne.surface_nakai_moishezon_literal` | `KltDP.Literature.Hartshorne.SurfaceNakaiMoishezon` | R. Hartshorne, Algebraic Geometry, GTM 52, Springer (1977); theorem Theorem V.1.10 (Nakai-Moishezon criterion); page 365; doi 10.1007/978-1-4757-3849-0 |
| 12 | `KltDP.Literature.Hartshorne.surface_riemannRoch_literal` | `KltDP.Literature.Hartshorne.SurfaceRiemannRoch` | R. Hartshorne, Algebraic Geometry, GTM 52, Springer (1977); theorem Theorem V.1.6 (Riemann-Roch for surfaces); page 362; doi 10.1007/978-1-4757-3849-0 |
| 13 | `KltDP.Literature.Keel.semiampleness_completeSystem_literal` | `KltDP.Literature.KeelCompleteSystem` | S. Keel, Basepoint freeness for nef and big line bundles in positive characteristic, Annals of Mathematics 149 (1999), 253-286; theorem Theorem 0.2; page 254; doi 10.2307/121025 |
| 14 | `KltDP.Literature.Stacks.affine_morphism_cohomology_literal` | `KltDP.Literature.Stacks.AffineMorphismCohomology` | The Stacks Project; lemma 30.2.4; tag 089W |
| 15 | `KltDP.Literature.Stacks.blowupRegularPoint_literal` | `KltDP.Literature.Stacks.BlowupRegularPointAdmitted` | The Stacks Project; R. Hartshorne, Algebraic Geometry, GTM 52, Springer (1977); theorem Hartshorne Proposition V.3.1; tags 0AGQ, 0AGR, 0C5P |
| 16 | `KltDP.Literature.Stacks.closed_point_blowups_dominate_proper_literal` | `KltDP.Literature.StacksPointBlowupDomination` | The Stacks Project; tag 0AHI |
| 17 | `KltDP.Literature.Stacks.field_isJ2` | `KltDP.Literature.Stacks.FieldJ2` | Stacks Project tag 07PJ item 1, commit 540451b3e79a (historical v6 entry) |
| 18 | `KltDP.Literature.Stacks.lipman_resolution_of_normal_completions_literal` | `KltDP.Literature.LipmanResolutionLiteral` | The Stacks Project; theorem Theorem 54.14.5, implication (4) => (2); tag 0BGP |
| 19 | `KltDP.Literature.Stacks.properCohomology_finite` | `KltDP.Literature.Stacks.ProperCohomologyFinite` | Stacks Project tag 02O6, commit 540451b3e79a (historical v6 entry) |
| 20 | `KltDP.Literature.Stacks.properFlat_fiberEuler_literal` | `KltDP.Literature.Stacks.ProperFlatFiberEuler` | The Stacks Project; lemma 36.32.2; tag 0B9T |
| 21 | `KltDP.Literature.Stacks.proper_curve_pullback_degree_literal` | `KltDP.Literature.ProperCurvePullbackDegreeLiteral` | The Stacks Project; tag 0AYZ |
| 22 | `KltDP.Literature.Stacks.proper_curve_tensor_degree_literal` | `KltDP.Literature.Stacks.CurveTensorDegreeLiteral` | Stacks Project tag 0AYX, lemma 33.44.7, commit 540451b3e79a (historical v6 entry) |
| 23 | `KltDP.Literature.Stacks.regularLocal_isUFD` | `KltDP.Literature.Stacks.RegularLocalUFD` | Stacks Project tag 0AG0, commit 540451b3e79a (historical v6 entry) |
| 24 | `KltDP.Literature.Stacks.regular_smooth_loci_perfect_literal` | `KltDP.Literature.RegularSmoothLociLiteral` | The Stacks Project; lemma 33.25.8; tag 0B8X |
| 25 | `KltDP.Literature.Stacks.smooth_standardSmooth_cover_literal` | `KltDP.Literature.SmoothStandardCoverLiteral` | The Stacks Project; lemma 10.137.9, first cover assertion; tag 00TA |
| 26 | `KltDP.Literature.Stacks.steinFactorization_noetherian_literal` | `KltDP.Literature.SteinFactorizationNoetherian` | The Stacks Project; tag 03H0 |
| 27 | `KltDP.Literature.Tanaka.contraction_44_instance` | `KltDP.Literature.Tanaka.ContractionTheorem` | H. Tanaka, Minimal model program for excellent surfaces, Annales de l'Institut Fourier 68 (2018), no. 1, 345-376; theorem Theorem 4.4, instance with B = S = Spec k, Delta = 0, conclusions (1), (2), (4); page 365; doi 10.5802/aif.3163 |
| 28 | `KltDP.Literature.Zariski.closedPoint_normal_completion_literal` | `KltDP.Literature.ZariskiNormalCompletion` | O. Zariski, Sur la normalite analytique des varietes normales, Annales de l'Institut Fourier 2 (1950); theorem Theorem 2; page 162 |

The four entries marked historical carry `original_registry` pointers to their unchanged v6
registries (`audit/field_j2_admission.json`, `audit/regular_local_ufd_admission.json`,
`audit/proper_cohomology_admission.json`, `audit/curve_tensor_degree_admission.json`), which are
kept as history and rehashed by the parser when present. For those four entries the v7 registry
reproduces the v6 module, source hash, universe parameters and both type hashes exactly. The type
hashes of all 28 entries were computed with `KltDP.Audit.Trust.declarationJsonCached` on the same
sources in a copy of the build lane, and the parser re-verifies them against the production trust
report.

## What changed from v6 to v7

| Component | v6 | v7 |
| --- | --- | --- |
| `KltDP/Audit/Trust.lean`: `literatureAxioms` | four Stacks names | the twenty-eight names above |
| `KltDP/Audit/Trust.lean`: `literatureModules` | none | explicit name-to-module table, checked against `literatureAxioms` at run time |
| `KltDP/Audit/Trust.lean`: `validateLiteratureShape` | four entries validated when present | every entry must exist in the checked environment, be a safe `axiom`, have a declaration range and be owned by its listed module; the four historical pinned `Expr` type comparisons are unchanged |
| `KltDP/Audit/Trust.lean`: `compilerCachePolicy` | `..._four_stacks_v6` | `..._twentyeight_admissions_v7` |
| `KltDP/Audit/Trust.lean`: everything else | | unchanged: scopes, closure traversal, cache and unsafe-implementation classification, runtime companions, emission format |
| `scripts/audit_sources.py`: `SOURCE_POLICY_PROFILE` | v6 string | v7 string |
| `scripts/audit_sources.py`: `axiom` | rejected everywhere, discharged by four hash-pinned helper modules | rejected everywhere except the twenty-eight allowlisted files (`LITERATURE_AXIOM_FILES`), each of which must contain exactly one `axiom` token; zero or several is fatal; optional cross-check against the registry (schema, policy, entry order, source hashes) |
| `scripts/audit_sources.py`: every other lexical rule | | unchanged: rejected leaf names and prefixes, reviewed attribute forms, reviewed declaration attributes, import gate, review-blocks-admission |
| `scripts/parse_compiled_audit256cpu4.py`: admission validation | four validators replaying probe/qualification evidence through four helper scripts and `audit/literature_allowlist.json` | one validator over `audit/literature-assumptions.json`: bound byte-identically in both build snapshots and locally; entries in canonical order; module and source path fixed by the admission table; source hash equal in both snapshots and locally; universe parameters and both type hashes checked against the emitted inventory row; non-empty `published_source`; historical pointers required for the four v6 entries only |
| `scripts/parse_compiled_audit256cpu4.py`: pins | `SOURCE_LINTER_SHA256`, `NATIVE_TOOLING_SHA256` for v6 files | re-pinned to the v7 linter and v7 `Trust.lean` |
| `scripts/parse_compiled_audit256cpu4.py`: roles/profiles | library, audit, four historical probe roles | library and audit; profiles `standard26` and `memory256cpu4` |
| `scripts/parse_compiled_audit256cpu4.py`: scoped mode | none | `--itemize-nonroot-failures ROOT...` (below); without the flag the strict certificate is unchanged |
| `scripts/parse_compiled_audit256cpu4.py`: module completeness | every library module must own an inventory row | unchanged, except that a module with no inventory row whose exact source is declaration-free (below) is accepted and itemized under `declaration_free_modules`; applies in both modes |
| Tests | `scripts/test_parse_compiled_*.py` (v6 helper contracts) | `scripts/test_parse_compiled_audit_v7.py`: synthetic inventory, registry, itemize-mode and source-gate fixtures; the source-gate tests run the real v7 linter on a synthetic tree |
| Registry | four per-entry registries plus an allowlist file | `audit/literature-assumptions.json` (schema `klt-literature-assumptions-v7`) |
| Runner profile | `standard26` (26 GiB) | `memory256cpu4` (4 CPUs, 256 GiB, no swap) via `run_build256cpu4.sh` / `scope_exec256cpu4.py`, copies of the 128 GiB variants with only the limit changed |

## The scoped mode `--itemize-nonroot-failures`

The strict certificate (`snapshot_dependency_policy_validated`) requires zero failed declarations and
`source_lint_passed`. The scoped mode emits a certificate with status
`passed_with_itemized_nonroot_failures` if and only if all of the following hold, and refuses otherwise:

1. Every `KLT_TRUST_FAILURE` names a declaration whose name ends in `._unsafe_rec`, whose owner (the
   name without the suffix) is a checked `opaque` declaration in the same module that itself passes
   the policy, which is a `partial`, safe-flagged `definition`, and whose closure fails only through
   `partial_dependencies` that are themselves such companions: no forbidden axiom, no missing, unsafe
   or tooling dependency. This is the exact shape Lean 4.19 gives a source-level `partial def`.
2. The audit exited with Lean status 1 and printed exactly one rejection message naming the same
   failure count as the summary and the failure records (or, with no failures, exited 0 without one);
   no other Lean error appears in the log.
3. Every listed logical root is in the inventory, passes the policy and has an empty
   partial-dependency list; independently, no failed declaration is reachable from it along the
   exported `direct_dependencies` edges (every dependency path between project declarations stays
   inside the project inventory, so this replays the auditor's reachability restricted to the project).
4. Every source-lint rejection is an `elab` or `partial` token; import-gate rejections stay fatal; all
   rejections and review findings are reproduced from the bound bytes and listed.

Every other record, closure, cache, unsafe-implementation, registry, source-gate and native-type check
is the strict one. The certificate lists the failures with their owners and modules, the roots with
their closure verdicts and reachability counts, and every source finding; it carries
`dependency_policy_status` and `audit_exit_code` so that it cannot be mistaken for the strict one.

## The metaprogramming modules

The twelve modules are `KltDP.Geometry.AdjunctionTensorRestrictionNativeBaseProof`, `KltDP.Geometry.GluedAdjunctionIntrinsicSourceProofAnnotations`, `KltDP.Geometry.GluedAdjunctionIntrinsicTargetNativeData`, `KltDP.Geometry.GluedAdjunctionIntrinsicTargetOriginalPrefunctor`, `KltDP.Geometry.GluedAdjunctionIntrinsicTargetProofAnnotations`, `KltDP.Geometry.GluedAdjunctionNativeApplication`, `KltDP.Geometry.GluedAdjunctionNativeApplicationTerm`, `KltDP.Geometry.GluedAdjunctionNativeComponentNormalization`, `KltDP.Geometry.GluedAdjunctionOriginalComponentNormalization`, `KltDP.Geometry.GluedAdjunctionSectionEqComposition`, `KltDP.Geometry.SchemeModulePullbackBoolFactorTerm`, `KltDP.Geometry.SchemeModulePullbackNativeFactorTerm`.
The v7 lint reports 24 rejections there (15 `elab`, 9 `partial`) and, across
139 files, 168 review findings (129 `attribute`, 12 declaration attribute `@[reassoc (attr := simp)]`, 11 `string_with_brace`, 5 declaration attribute `@[simps]`, 2 declaration attribute `@[simps! source target iso]`, 1 declaration attribute `@[refl, simps]`, 1 declaration attribute `@[symm, simps]`, 1 declaration attribute `@[trans, simps! source target iso]`, 1 declaration attribute `@[stacks 0A20      ]`, 1 declaration attribute `@[refl]`, 1 declaration attribute `@[symm]`, 1 declaration attribute `@[trans]`, 1 declaration attribute `@[mk_iff]`, 1 declaration attribute `@[simps! apply_apply symm_apply]`).
All of these lie outside the candidate1559 subset. They are recorded as reviewed findings; none is
discharged. The elaborators are unreviewed elaboration-time code; the declarations they produce are
kernel-checked terms that the auditor traverses like any other.

The 9 failed declarations, all `partial def` companions:

| Failed declaration | Module | Owner (kind) | Partial dependencies |
| --- | --- | --- | --- |
| `_private.KltDP.Geometry.AdjunctionTensorRestrictionNativeBaseProof.0.KltDP.Geometry.AdjunctionTensorRestrictionNativeBaseProof.headZeta._unsafe_rec` | `KltDP.Geometry.AdjunctionTensorRestrictionNativeBaseProof` | `headZeta` (opaque) | itself |
| `_private.KltDP.Geometry.GluedAdjunctionIntrinsicSourceProofAnnotations.0.KltDP.Geometry.GluedAdjunctionIntrinsicSourceProofAnnotations.headZeta._unsafe_rec` | `KltDP.Geometry.GluedAdjunctionIntrinsicSourceProofAnnotations` | `headZeta` (opaque) | itself |
| `_private.KltDP.Geometry.GluedAdjunctionIntrinsicTargetNativeData.0.KltDP.Geometry.GluedAdjunctionIntrinsicTargetNativeData.headZeta._unsafe_rec` | `KltDP.Geometry.GluedAdjunctionIntrinsicTargetNativeData` | `headZeta` (opaque) | itself |
| `_private.KltDP.Geometry.GluedAdjunctionIntrinsicTargetOriginalPrefunctor.0.KltDP.Geometry.GluedAdjunctionIntrinsicTargetOriginalPrefunctor.headZeta._unsafe_rec` | `KltDP.Geometry.GluedAdjunctionIntrinsicTargetOriginalPrefunctor` | `headZeta` (opaque) | itself |
| `_private.KltDP.Geometry.GluedAdjunctionIntrinsicTargetProofAnnotations.0.KltDP.Geometry.GluedAdjunctionIntrinsicTargetProofAnnotations.headZeta._unsafe_rec` | `KltDP.Geometry.GluedAdjunctionIntrinsicTargetProofAnnotations` | `headZeta` (opaque) | itself |
| `_private.KltDP.Geometry.GluedAdjunctionNativeComponentNormalization.0.KltDP.Geometry.GluedAdjunctionNativeComponentNormalization.headZeta._unsafe_rec` | `KltDP.Geometry.GluedAdjunctionNativeComponentNormalization` | `headZeta` (opaque) | itself |
| `_private.KltDP.Geometry.GluedAdjunctionOriginalComponentNormalization.0.KltDP.Geometry.GluedAdjunctionOriginalComponentNormalization.headZeta._unsafe_rec` | `KltDP.Geometry.GluedAdjunctionOriginalComponentNormalization` | `headZeta` (opaque) | itself |
| `_private.KltDP.Geometry.GluedAdjunctionSectionEqComposition.0.KltDP.Geometry.GluedAdjunctionSectionEqComposition.localHead._unsafe_rec` | `KltDP.Geometry.GluedAdjunctionSectionEqComposition` | `localHead` (opaque) | itself |
| `_private.KltDP.Geometry.SchemeModulePullbackNativeFactorTerm.0.KltDP.Geometry.SchemeModulePullbackNativeFactorTerm.headZeta._unsafe_rec` | `KltDP.Geometry.SchemeModulePullbackNativeFactorTerm` | `headZeta` (opaque) | itself |

The three logical roots, from the trust report and the certificate's reachability replay:

| Root | Kind | Closure size (incl. root) | Reachable project declarations | Transitive axioms | Ordinary declarations reached in the twelve modules |
| --- | --- | --- | --- | --- | --- |
| `KltDP.Manuscript.uniformSevenPointBound` | theorem | 96,411 | 22,215 in 2,544 modules | 31 (28 literature) | 8 (all policy-passing) |
| `KltDP.Manuscript.S01.sharpnessExampleCharThree` | theorem | 84,393 | 18,317 in 1,901 modules | 12 (9 literature) | none |
| `KltDP.Manuscript.S01.characteristicTwoFamily` | theorem | 84,397 | 18,318 in 1,901 modules | 12 (9 literature) | none |

The main theorem reaches 8 ordinary, policy-passing declarations (theorems and definitions
whose proofs were produced by the custom elaborators and then kernel-checked) in 6 of the twelve
modules; it reaches none of the elaborators or companions. The two examples reach none of the twelve
modules.

## Declaration-free modules

5 library modules contain no declaration: their sources consist only of `import`, `#check` and
`#print axioms` commands, or of an `import` followed by a module docstring. The trust report therefore has
no inventory row for them, and the first scoped parser run refused with
`Compiled audit validation FAILED: Library mathematical modules absent from inventory: KltDP.Geometry.AffineStalkCompletionExports, KltDP.Geometry.RegularProperCurveFieldIsoAudit, KltDP.Geometry.RuledSurfaceSourceGeometryAudit, KltDP.Geometry.SingularStalkCompletionNormalExports, KltDP.Geometry.SmoothPointBlowupAffineCanonicalCharts` (stage `parser_itemized_refused` below). The completeness rule was amended: a module
with no inventory row is accepted only if a scan of its exact archived source, after masking comments,
docstrings and strings with the reviewed linter's lexer (`mask_noncode`), finds nothing but `import`,
`open`, `namespace`, `section`, `end`, `universe`, `variable`, `set_option`, `#check` and `#print`
commands in their one-line forms with identifier arguments (no `in` combinators, no `#eval`, no
`#guard_msgs`, no declaration keyword anywhere in the code); every other module remains subject to the
rule, and a declaration-free module may not own any inventory row. The certificate lists them, with their
archived source hashes and command counts, under `declaration_free_modules`:

| Module | Commands | Source sha256 |
| --- | --- | --- |
| `KltDP.Geometry.AffineStalkCompletionExports` | `import` 1, `#check` 7, `#print` 7 | `afcf5ae96392b0b169a95b1f7d34ce64030dadfe3a5262685bd8a51905157fa6` |
| `KltDP.Geometry.RegularProperCurveFieldIsoAudit` | `import` 1, `#print` 2 | `db5f50b1334c5014d84317baee0b2e91ad68fea33261f10f6b528d91cf3fd130` |
| `KltDP.Geometry.RuledSurfaceSourceGeometryAudit` | `import` 1, `#check` 7, `#print` 7 | `a47740f92450dce2f39020a418cf2022f926c03c41396165130527486fa3b4d9` |
| `KltDP.Geometry.SingularStalkCompletionNormalExports` | `import` 1, `#check` 3, `#print` 3 | `67b6f31db614eca9f95e79c7c65dfe6e4c8b9237f0e44beaed24c9136d5fdbaa` |
| `KltDP.Geometry.SmoothPointBlowupAffineCanonicalCharts` | `import` 1 | `c8bc21c9274ee1cce1c692462f5738a1cf0c743befdb776f4e4c02848dc9e7b7` |

## The run

All Lean, Lake and parser jobs ran on the build VM through the capped runner `run_build256cpu4.sh`
(4 CPUs, 256 GiB, no swap; runner root `/home/david/klt-final-cmp/runner`) on the staged project
`/home/david/klt-final-cmp/project`, built from scratch (no prebuilt objects; Mathlib objects come
from the shared pinned package checkout). The staged tree is byte-identical to the packaged tarball
for every Lean and Lake file except `KltDP/Audit/Trust.lean` (v7 tooling); the added files are the
v7 scripts, the registry, the source-lint report, the four historical registries and the axiom probe.

| Stage | Build ID | Command | Exit | Started (UTC) | Duration |
| --- | --- | --- | --- | --- | --- |
| library | `20260918T021510Z-1719539` | `lake build KltDP KltDP.Audit.Trust` | 0 | 2026-09-18T02:15:10Z | 4:13:53 |
| audit | `20260918T062905Z-1962699` | `lake env lean audit/CompiledTrust.lean` | 1 | 2026-09-18T06:29:05Z | 8:16:30 |
| parser_strict | `20260918T144537Z-2308083` | `lake env python3 scripts/parse_compiled_audit256cpu4.py --project /home/david...` | 1 | 2026-09-18T14:45:37Z | 0:00:01 |
| probe | `20260918T144538Z-2308230` | `lake env lean audit/FinalAxiomsProbe.lean` | 0 | 2026-09-18T14:45:38Z | 0:00:25 |
| parser_itemized_refused | `20260918T144634Z-2308452` | `lake env python3 scripts/parse_compiled_audit256cpu4.py --project /home/david...` | 1 | 2026-09-18T14:46:34Z | 0:01:36 |
| parser_itemized | `20260918T150124Z-2309692` | `lake env python3 scripts/parse_compiled_audit256cpu4.py --project /home/david...` | 0 | 2026-09-18T15:01:24Z | 0:02:40 |
| summary | `20260918T144810Z-2308659` | `lake env python3 scripts/summarize_trust_report.py /home/david/klt-final-cmp/...` | 0 | 2026-09-18T14:48:10Z | 0:00:48 |

The library build log holds 2,329,371 bytes; the trust report holds
7,376,783,576 bytes (sha256
`29f9703cc90356a4e6e6ffb5f52d3932ecc2cd79fe66aa86867653d97ba7bbd5`); the parsed full inventory
`production_v5_final_validation.records.json` holds 7,507,684,267 bytes (sha256
`b758c02d8c7c5c421a01e5537a07dddff5a598d56168a2463b60dca5be0a90f9`). Both large files stay on the build VM; their hashes are in the
checkpoint.

## Results

Trust report (`KLT_TRUST_AUDIT`): 41,652 mathematical declarations, 32 runtime
companions, 3,538 compiler stage caches, 24,699 unsafe implementation records,
71,351 inventory rows in total; `failed_declaration_count = 9`; status
`dependency_policy_failed`; transitive axioms over all logical roots: 31 names (3 foundations +
28 literature); `literature_axioms`: 28 names.

Scoped certificate: status `passed_with_itemized_nonroot_failures`, itemized failures 9, itemized source
rejections 24, itemized review findings 168, declaration-free modules
5; validated at 2026-09-18T15:04:02.094971+00:00.

The strict parser (stage `parser_strict`) refused with: `Compiled audit validation FAILED: audit: exit was not zero`.

Axiom probe (`audit/FinalAxiomsProbe.lean`, `#print axioms` for the three roots; stage `probe` in the table):

```
'KltDP.Manuscript.uniformSevenPointBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 KltDP.Literature.Hartshorne.castelnuovo_contraction_literal,
 KltDP.Literature.Hartshorne.hasContractionLifts_instance,
 KltDP.Literature.Hartshorne.hurwitz_degreeTwo_projectiveLine_instance,
 KltDP.Literature.Hartshorne.integral_numerical_group_free_finite_literal,
 KltDP.Literature.Hartshorne.minimal_surface_classification_literal,
 KltDP.Literature.Hartshorne.nonsingular_complete_surface_projective_literal,
 KltDP.Literature.Hartshorne.point_blowup_structure_cohomology_literal,
 KltDP.Literature.Hartshorne.ruled_surface_genus_literal,
 KltDP.Literature.Hartshorne.ruled_surface_picard_literal,
 KltDP.Literature.Hartshorne.surface_hodge_index_literal,
 KltDP.Literature.Hartshorne.surface_nakai_moishezon_literal,
 KltDP.Literature.Hartshorne.surface_riemannRoch_literal,
 KltDP.Literature.Keel.semiampleness_completeSystem_literal,
 KltDP.Literature.Stacks.affine_morphism_cohomology_literal,
 KltDP.Literature.Stacks.blowupRegularPoint_literal,
 KltDP.Literature.Stacks.closed_point_blowups_dominate_proper_literal,
 KltDP.Literature.Stacks.field_isJ2,
 KltDP.Literature.Stacks.lipman_resolution_of_normal_completions_literal,
 KltDP.Literature.Stacks.properCohomology_finite,
 KltDP.Literature.Stacks.properFlat_fiberEuler_literal,
 KltDP.Literature.Stacks.proper_curve_pullback_degree_literal,
 KltDP.Literature.Stacks.proper_curve_tensor_degree_literal,
 KltDP.Literature.Stacks.regularLocal_isUFD,
 KltDP.Literature.Stacks.regular_smooth_loci_perfect_literal,
 KltDP.Literature.Stacks.smooth_standardSmooth_cover_literal,
 KltDP.Literature.Stacks.steinFactorization_noetherian_literal,
 KltDP.Literature.Tanaka.contraction_44_instance,
 KltDP.Literature.Zariski.closedPoint_normal_completion_literal]
'KltDP.Manuscript.S01.sharpnessExampleCharThree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 KltDP.Literature.Hartshorne.nonsingular_complete_surface_projective_literal,
 KltDP.Literature.Hartshorne.surface_riemannRoch_literal,
 KltDP.Literature.Keel.semiampleness_completeSystem_literal,
 KltDP.Literature.Stacks.closed_point_blowups_dominate_proper_literal,
 KltDP.Literature.Stacks.field_isJ2,
 KltDP.Literature.Stacks.properCohomology_finite,
 KltDP.Literature.Stacks.proper_curve_tensor_degree_literal,
 KltDP.Literature.Stacks.regularLocal_isUFD,
 KltDP.Literature.Stacks.steinFactorization_noetherian_literal]
'KltDP.Manuscript.S01.characteristicTwoFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 KltDP.Literature.Hartshorne.nonsingular_complete_surface_projective_literal,
 KltDP.Literature.Hartshorne.surface_riemannRoch_literal,
 KltDP.Literature.Keel.semiampleness_completeSystem_literal,
 KltDP.Literature.Stacks.closed_point_blowups_dominate_proper_literal,
 KltDP.Literature.Stacks.field_isJ2,
 KltDP.Literature.Stacks.properCohomology_finite,
 KltDP.Literature.Stacks.proper_curve_tensor_degree_literal,
 KltDP.Literature.Stacks.regularLocal_isUFD,
 KltDP.Literature.Stacks.steinFactorization_noetherian_literal]
```

The three printed sets equal the sets recorded for these roots in the trust report and, for the main
theorem, the list in `manuscript_formalization_20260916/FINAL_AXIOMS.txt`.

## Files

| File | sha256 |
| --- | --- |
| `KltDP/Audit/Trust.lean` | `c5f4646aaccc523bcdc4e626fd3387575c3260c1a867468a2b28665170e39bce` |
| `scripts/audit_sources.py` | `011042a01c2e6389ed4182c6917db345e4a68b1889c5cde8806548800f6c9af3` |
| `scripts/parse_compiled_audit256cpu4.py` | `a495c23e5e1bf4a61af41b396e304d9aa1296295f110e5961d2ec633bd35fa16` |
| `scripts/test_parse_compiled_audit_v7.py` | `f839d79313169f25cbc076bf9f61e6cd920399ad62e4358ef4c9499dfe64af50` |
| `scripts/summarize_trust_report.py` | `bcc767e014239f8b4d72d99f1fffaf9015decf491a16288e32bf6866e27733b7` |
| `audit/literature-assumptions.json` | `78b23d3f9adec6e4a00422ff1866f0a682d725cd1842f0994206481549f951c1` |
| `audit/FinalAxiomsProbe.lean` | `577fd2611234e5bae0216875c83c51fb0544c5b1c91ede8fb8aa2285e587bfe6` |
| `audit/CompiledTrust.lean` | `be82fe238892c7279abb14e2c608afecc87fbd0abcbe02bbf8994d67b3ad0f2a` |
| `audit/source_lint.json` | `730c1d176c5a146c7dde9f5472318a216833ea1a62f38e67703ff8515a96b708` |
| `audit/checkpoints/final-2026-09/production_v5_final_validation.json` | `456335f5557e5e9e9606dc5be43fc8d5015ce94568f834fa995c0da521a65a39` |
| `audit/checkpoints/final-2026-09/production_v5_final_validation.json.gz` | `85bcea78bf1802bbc059c0f338e8fab51ff7e5ae81da190a38ee6792e1182fda` |
| `audit/checkpoints/final-2026-09/trust_summary.json` | `fdf0629f5e3348ad1128650cf75e7f732db3f0d759a374e602b471eccac50813` |
| `audit/checkpoints/final-2026-09/probe_print_axioms.txt` | `6c071a7635319f5d57060f937b92ff603c85d9203f61b812309cbc9b6d6d9959` |
| `audit/checkpoints/final-2026-09/configuration.json` | `9413a6ace920954dd9930f06ff69932d8133e55223f4561edd56a8df9ad12fdd` |
| `audit/checkpoints/final-2026-09/oleans_before.json` | `de061e7447ece9fce9fea51b808b8bc0523b6217bd8b22385b8a978ef48c7f8b` |
| `audit/checkpoints/final-2026-09/oleans_after.json` | `aa9c82a500435c5e8eb645d68319ac7620dcd9dddae4df5e9bb744679a8918c4` |

`audit/checkpoints/final-2026-09/records/<stage>-<build id>/` holds `inputs.json`, `outputs.json`,
`cgroup.json`, `command.sh`, `exit_code.txt`, `started_at.txt`, `completed_at.txt`, `project.txt`
and, except for the multi-GB audit log, `build.log`; `SHA256SUMS` lists every checkpoint file.
