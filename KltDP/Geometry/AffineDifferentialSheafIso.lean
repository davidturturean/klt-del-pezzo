import KltDP.Geometry.SchemeKaehlerOpenRestriction
import KltDP.Geometry.AffineKaehlerTildeLocalization
import KltDP.Geometry.AffineFiniteType

/-!
# The differential sheaf on an affine open is the tilde of its Kähler module

BRIEF33 item 1, the *sections bridge*, in its sheaf-level half.  On an affine open `W` of a `k`-scheme
the global differential sheaf becomes the tilde of `Ω[Γ(X, W)⁄k]`, which is what lets the overlap
route read frames off the chart ring (`KaehlerLocalizedFrame`) instead of off free-sheaf sections.

The transport is the `eqToIso`-carrying one, so it is **not** invented here: it mirrors, step for step,
the accepted `SmoothKaehlerLocallyFree.exists_standardSmooth_open_freeIso`, with that proof's `free`
factor (`standardSmoothAffineFreeIso`, `mapFreeIso`, `restrictionUnitIso`) dropped and the accepted
`AffineKaehlerTildeLocalization.iso` put in its place.  The four accepted steps are

* `SchemeKaehlerOpenRestriction.restrictionIso f W.ι` — restricting `Ω_{X/k}` to the open subscheme,
* `eqToIso (congrArg baseRingSheaf hj)` — the square `hj : isoSpec.hom ≫ g = W.ι ≫ f`, exactly the
  accepted proof's `e₂`,
* `SchemeKaehlerOpenRestriction.restrictionIso g (hW.isoSpec.hom)` — transporting along the affine
  identification,
* `AffineKaehlerTildeLocalization.iso k Γ(X, W)` — the affine comparison with the tilde.

The `k`-algebra structure on `Γ(X, W)` is the one the accepted proof uses,
`(baseToAffineSectionsMap f hW).hom.toAlgebra`, and it is introduced in the statement by `letI` in the
accepted `InvertibleSheafPicard` style, because the type mentions `differentialModule k Γ(X, W)`.

Nothing is admitted here.  This module states no sections-level consequence; evaluating this
isomorphism is `AffineDifferentialSections`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf KltDP.Geometry.SchemeKaehlerOpenRestriction
open KltDP.Geometry.SchemeModuleRestriction KltDP.Geometry.AffineKaehlerTildeDerivation

universe u

namespace KltDP.Geometry.AffineDifferentialSheafIso

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **The differential sheaf restricted to an affine open is the tilde of its Kähler module.**
Mirrors the accepted `exists_standardSmooth_open_freeIso` transport, without its `free` factor. -/
def affineDifferentialIso {W : X.Opens} (hW : IsAffineOpen W) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    (restriction W.ι).obj (baseRingSheaf f) ≅
      (restriction hW.isoSpec.hom).obj ((differentialModule k Γ(X, W)).tilde) := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  let j := hW.isoSpec.hom
  let g := Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, W)))
  have hj : j ≫ g = W.ι ≫ f := by
    change hW.isoSpec.hom ≫ Spec.map (baseToAffineSectionsMap f hW) = W.ι ≫ f
    rw [Spec_map_baseToAffineSectionsMap f hW, ← Category.assoc,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec]
  let e₂ : baseRingSheaf (j ≫ g) ≅ baseRingSheaf (W.ι ≫ f) :=
    eqToIso (congrArg baseRingSheaf hj)
  exact restrictionIso f W.ι ≪≫ e₂.symm ≪≫ (restrictionIso g j).symm ≪≫
    (restriction j).mapIso (AffineKaehlerTildeLocalization.iso k Γ(X, W))

end KltDP.Geometry.AffineDifferentialSheafIso
