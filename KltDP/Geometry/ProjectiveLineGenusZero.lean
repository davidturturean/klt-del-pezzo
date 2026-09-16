import KltDP.Geometry.ProjectiveLineHOneVanishing
import KltDP.Geometry.QuasicoherentOpenRestriction
import KltDP.Compatibility.InvertibleQuasicoherent
import KltDP.Literature.AffineVanishingLiteral

/-!
# `g(P¹) = 0` from the affine-vanishing literal (Stacks 01XB) and the open-`Ext` comparison

Nothing is admitted here. `KltDP.Literature.Stacks.AffineVanishingLiteral` (Stacks 01XB, affine-scheme form) and
`OpenExtComparison` (a named mathematical hypothesis, not a literature statement) enter as explicit hypotheses.

* **`affineVanishing_restriction`**: the literal gives the published affine-open form of 01XB: for a scheme `X`, a
  quasi-coherent `F`, an affine open `U` and `p > 0`, `H^p(U, F|_U) = 0` (accepted restriction
  `SchemeModuleRestriction.restriction U.ι` and the accepted instance `isQuasicoherent_restriction`).
* **`unit_isQuasicoherent`**: the structure sheaf of a scheme is quasi-coherent (accepted `unit_isInvertible`,
  `IsInvertible.isLocallyFree`, `locallyFree_isQuasicoherent`).
* **`OpenExtComparison`** (named hypothesis): for every scheme `X`, open `U`, module `M` and `p`, an additive
  equivalence `Ext^p_X(ℤ[U], M) ≃+ H^p(U, M|_U)` between the pinned `Ext` out of the free abelian sheaf on `U`
  (`ProjectiveLineHOneVanishing.freeSheaf`) and the accepted Zariski cohomology of the restricted module.
  Mathematically this is Stacks 01E1 (restriction to `U` preserves injectives, `j_!` being an exact left adjoint)
  together with `Hom(ℤ[U], I) ≅ I(U)`; the pinned Mathlib has no extension by zero, so it is not proved here.
* **`genus_projectiveLine_eq_zero (hV) (hE) : g(P¹) = 0`**: via `ProjectiveLineHOneVanishing.genus_projectiveLine_eq_zero_of_affine`
  (lane D, compiled and queued, not yet accepted), the two standard charts being affine opens.

Open: `OpenExtComparison` itself (its degree-one vanishing form is proved in `OpenRestrictionExtOne`, which
removes `hE` from the genus statement) and the admission of the literal.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian Opposite TopologicalSpace AlgebraicGeometry
open KltDP.Geometry.ProjectiveLineComparison KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.ProjectiveLineSections KltDP.Geometry.ProjectiveLineHOneVanishing
open KltDP.Literature.Stacks

universe u

namespace KltDP.Geometry.ProjectiveLineGenusZero

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The affine-scheme literal gives the published affine-open form of Stacks 01XB:
`H^p(U, F|_U) = 0` for `p > 0`, every affine open `U` and every quasi-coherent `F`. -/
theorem affineVanishing_restriction (hV : AffineVanishingLiteral.{u}) {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p) :
    Subsingleton (H ((SchemeModuleRestriction.restriction U.ι).obj F) p) := by
  haveI : IsAffine U.toScheme := hU
  exact hV.subsingleton_H U.toScheme ((SchemeModuleRestriction.restriction U.ι).obj F) p hp

/-- The structure sheaf of a scheme is quasi-coherent. -/
theorem unit_isQuasicoherent (X : Scheme.{u}) :
    (_root_.SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  inferInstance

/-- **Named hypothesis (not a literature statement, not an axiom).** For every open `U` of a scheme `X`, every
module `M` and every degree `p`, `Ext^p_X(ℤ[U], M) ≃+ H^p(U, M|_U)`, with the pinned `Ext` out of the free
abelian sheaf on `U` and the accepted Zariski cohomology of the accepted restriction. -/
structure OpenExtComparison : Prop where
  nonempty_addEquiv : ∀ (X : Scheme.{u}) (U : X.Opens) (M : X.Modules) (p : ℕ),
    Nonempty (Ext (freeSheaf (J := Opens.grothendieckTopology X) U)
        ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) p ≃+
      H ((SchemeModuleRestriction.restriction U.ι).obj M) p)

/-- `Ext¹(ℤ[U_i], O_{P¹}) = 0` on the two standard charts, from the literal and the comparison. -/
theorem chart_ext_one_subsingleton_of_comparison (hV : AffineVanishingLiteral.{u})
    (hE : OpenExtComparison.{u}) (k : Type u) [Field k] (i : Fin 2) :
    Subsingleton (Ext (freeSheaf (J := Opens.grothendieckTopology (projectiveSpace k 1)) (chartOpen k i))
      (structureAbelianSheaf k) 1) := by
  haveI := unit_isQuasicoherent (projectiveSpace k 1)
  haveI := affineVanishing_restriction hV
    (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) (chartOpen k i)
    (chartOpen_isAffineOpen k i) 1 one_pos
  obtain ⟨e⟩ := hE.nonempty_addEquiv (projectiveSpace k 1) (chartOpen k i)
    (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) 1
  exact e.toEquiv.subsingleton

/-- **`g(P¹) = 0`**, conditional on the affine-vanishing literal (Stacks 01XB) and `OpenExtComparison`. -/
theorem genus_projectiveLine_eq_zero (k : Type u) [Field k] (hV : AffineVanishingLiteral.{u})
    (hE : OpenExtComparison.{u}) :
    CurveCanonical.genus (projectiveSpaceToSpec k 1) = 0 :=
  genus_projectiveLine_eq_zero_of_affine k (chart_ext_one_subsingleton_of_comparison hV hE k 0)
    (chart_ext_one_subsingleton_of_comparison hV hE k 1)

end KltDP.Geometry.ProjectiveLineGenusZero
