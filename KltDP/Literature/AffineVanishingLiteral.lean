import KltDP.Geometry.ModuleCohomology
import KltDP.Geometry.QuasicoherentOpenRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Stacks 01XB (affine vanishing) as an exact literature literal: a hypothesis, not admitted

NOTHING IS ASSUMED OR ADMITTED HERE. `AffineVanishingLiteral` is a `Prop`-valued structure. Consumers take it as
an explicit hypothesis; root decides at a checkpoint whether it is admitted (as for Stacks 0AYX).

Source: The Stacks Project, Tag 01XB = Lemma 30.2.2, Chapter 30 "Cohomology of Schemes", Section 30.2 (Tag 01X8)
"Čech cohomology of quasi-coherent sheaves"; `coherent.tex`, label `lemma-quasi-coherent-affine-cohomology-zero`,
lines 138–155 at stacks-project commit a04446e57ec1fbc252a871afcec7752fb2807b14 (fetched 2026-09-11 from
https://stacks.math.columbia.edu/tag/01XB and from the repository; dossier `laneD/AFFINE_VANISHING_LITERAL.md`):

  "The following lemma says in particular that for any affine scheme $X$ and any quasi-coherent sheaf
  $\mathcal{F}$ on $X$ we have $H^p(X, \mathcal{F}) = 0$ for all $p > 0$.

  Lemma 30.2.2. Let $X$ be a scheme. Let $\mathcal{F}$ be a quasi-coherent $\mathcal{O}_X$-module. For any
  affine open $U \subset X$ we have $H^p(U, \mathcal{F}) = 0$ for all $p > 0$."

Encoded: the affine-scheme form stated in the sentence introducing the lemma (the case `U = X`), with
* the scheme: `X : Scheme.{u}` with Mathlib's `IsAffine X` (no other hypothesis: no Noetherian, separated, finite
  type or base-field premise);
* the quasi-coherent `𝒪_X`-module: `F : X.Modules` (Mathlib's `SheafOfModules X.ringCatSheaf`) with the pinned
  `SheafOfModules.IsQuasicoherent` (the predicate of the accepted `QuasicoherentOpenRestriction`,
  `AffineQuasicoherentKernels`, `AffineModuleTildePresentation`);
* `H^p(X, F)`: the accepted `KltDP.Geometry.ModuleCohomology.H F p`, the pinned `Ext^p(ℤ, F)` of the underlying
  abelian sheaf on the Zariski site (Stacks computes `H^p` by an injective resolution in `Ab(X)` or in
  `Mod(𝒪_X)`; Tag 01DZ, and both agree);
* "`= 0` for all `p > 0`": `Subsingleton (H F p)` for `0 < p`.

The published affine-open form follows from this field by applying it to the open subscheme `U` with the accepted
restriction `F|_U` (Stacks Tag 01E1 (2): `H^p(U, F) = H^p(U, F|_U)`; accepted instance
`SchemeModuleRestriction.isQuasicoherent_restriction`); that derivation is the ordinary theorem
`ProjectiveLineGenusZero.affineVanishing_restriction`, not part of this literal.
-/

universe u

namespace KltDP.Literature.Stacks

open AlgebraicGeometry CategoryTheory

-- The permitted local instances, as in every accepted file stating `[M.IsQuasicoherent]` on `X.Modules`
-- (the over-site `WEqualsLocallyBijective` instances of `IsQuasicoherent` need them).
attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Stacks 01XB (Lemma 30.2.2), affine-scheme form: for every affine scheme `X` and every quasi-coherent
`𝒪_X`-module `F`, `H^p(X, F) = 0` for all `p > 0`, with the accepted Zariski cohomology `H`.
A hypothesis for consumers; not admitted. -/
structure AffineVanishingLiteral : Prop where
  subsingleton_H : ∀ (X : Scheme.{u}) [instAffine : IsAffine X] (F : X.Modules)
    [instQuasicoherent : F.IsQuasicoherent] (p : ℕ), 0 < p →
    Subsingleton (KltDP.Geometry.ModuleCohomology.H F p)

end KltDP.Literature.Stacks
