# Third-party notices

The copied Lean files retain their original copyright, author, license and adaptation notices. The [source-header inventory](audit/third-party-sources.json) identifies 240 files whose first comment records copyright, a license, or a source adaptation. This inventory is a guide to those notices, not a claim that all other files are original work.

Complete Apache 2.0 texts are supplied in [LICENSES/](LICENSES/README.md). A source header's generic reference to `LICENSE` refers to the applicable third-party text here. No project-wide license for original material is assigned by these copies.

## Mathlib

Compatibility ports retain their individual Mathlib authors, upstream paths and exact revisions. These include work credited to Joël Riou, Chris Birkbeck, Vasily Ilin, Justus Springer, Christian Merten, Kim Morrison, Andrew Yang, Brian Nugent, Raphael Douglas Giles and the other authors named in the retained headers. Each port records the adaptation to Lean 4.19 and the pinned Mathlib interfaces. The project dependency itself remains pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

The [complete Apache text](LICENSES/Apache-2.0.txt) and the original header-referenced license copies are retained. Porting a file from a newer Mathlib revision does not change the project's dependency pin.

## MazurTheorem and Lean Pool

Selected sheaf/cohomology arguments come through [MazurTheorem, revision 9327963](https://github.com/Vilin97/MazurTheorem/tree/9327963d4ec14fba49c7b14b004fd00707ffc2e9). The retained Grothendieck-vanishing notices credit Vasily Ilin and Brian Nugent, with [Lean Pool source revision 4eef1ff](https://github.com/Vilin97/lean-pool/tree/4eef1ffb3b643d606665e3b5585aa69454e137d1/LeanPool/GrothendieckVanishing). Upstream migration credits include Vasily Ilin, GitHub Actions and Claude Opus 5. The copied files record their local adaptations. See the [upstream notices](https://github.com/Vilin97/MazurTheorem/blob/9327963d4ec14fba49c7b14b004fd00707ffc2e9/THIRD_PARTY_NOTICES.md) and [license](LICENSES/MazurTheorem-Apache-2.0.txt).

## AINTLIB

Selected geometry and sheaf proofs credit Chris Birkbeck and the AINTLIB ModularCurves contributors. The headers identify the copied paths and adaptations. One source revision is `7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`; that revision has no root license, while selected files retain individual Apache notices. Separate repository-license evidence is [revision 1c1c746](https://github.com/CBirkbeck/AINTLIB/tree/1c1c74664e40071c2c2165bc55ca2616a67ccd6b). The selected headerless `SchemeModuleSheaf.lean` is byte-identical at both revisions, SHA-256 `4297f3874ba9b2dc670ddea0ed4b73d41c9fd9ee27e951f49a7bee5cd707f688`.

Additional ports name [revision 160e446](https://github.com/CBirkbeck/AINTLIB/tree/160e446617a2168c34c95bbe7a76c4105b392434), which separately supplies the same full [Apache license text](LICENSES/AINTLIB-Apache-2.0.txt). The source revision and license-evidence revision remain distinct provenance records.

## Tau Ceti

Tau Ceti contributor notices are retained. The ports use the [reviewed integration revision a74dfee](https://github.com/Vilin97/TauCeti/tree/a74dfee78f800df63f085a19006f7d502eee365e), based on [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) revision `a3913fd9111b851af857f720b4ce6721e6634183`. The exact copied files and compatibility changes are named in their headers. The [Apache license](LICENSES/TauCeti-Apache-2.0.txt) is included.

## UW Math AI

[NagataFactoriality.lean](KltDP/Compatibility/NagataFactoriality.lean) adapts the prime-localization argument from [UW Math AI's auslander-buchsbaum repository](https://github.com/uw-math-ai/auslander-buchsbaum/blob/ff45bce9228646c73f0dc0f40c1459f37d5c6307/Reference/Nagata%20theorem.lean), revision `ff45bce9228646c73f0dc0f40c1459f37d5c6307`. Its header describes the narrower imports and replacement of the source's multiset reconstruction by the pinned Mathlib factorization API. The complete Apache text is provided in [LICENSES/](LICENSES/README.md).

## Mathematical sources

The manuscript's references and the four [Stacks assumptions](notes/TRUST.md) supply mathematical attribution independently of code-port provenance. Third-party author credits do not identify the author of the frozen manuscript. Existing AI credits in source headers have been preserved as part of the upstream notices.
