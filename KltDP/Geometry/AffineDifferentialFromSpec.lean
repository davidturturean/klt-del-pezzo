import KltDP.Geometry.SchemeKaehlerOpenRestriction
import KltDP.Geometry.AffineKaehlerTildeLocalization
import KltDP.Geometry.AffineFiniteType

/-!
# The differential sheaf on the canonical affine chart of an affine open

`AffineDifferentialSheafIso.affineDifferentialIso` identifies `Ω_{X/k}` restricted along `W.ι` with
the tilde of `Ω[Γ(X, W)⁄k]` restricted along `hW.isoSpec.hom`, i.e. as sheaves on the open subscheme
`W.toScheme`.  This module states the same comparison one step further along, as sheaves on
`Spec Γ(X, W)`, by restricting along the canonical affine chart `hW.fromSpec` instead.

* **`affineDifferentialFromSpecIso`**:
  `(restriction hW.fromSpec).obj (baseRingSheaf f) ≅ (differentialModule k Γ(X, W)).tilde`.

**Why `fromSpec` rather than `W.ι`.**  Sections read off the `W.toScheme` presentation carry scalars
from `Γ(W.toScheme, ⊤)`, which pinned Mathlib calls only "non-reducibly defeq" to `Γ(X, W)`
(`AffineScheme.lean:348-349`); bridging them costs the `eqToIso`-based `Scheme.Opens.topIso`, and
rewriting `W.ι ''ᵁ ⊤ = W` moves a ring and a module together — the heterogeneous transport the lane
rules forbid.  The `Spec Γ(X, W)` presentation avoids the bridge entirely: the accepted
`AffineOpenModule` development already supplies `fromSpec_image_top : hW.fromSpec ''ᵁ ⊤ = W` and,
crucially, `sectionsOfImageEq_base_smul`, which states the section comparison's linearity over
`Γ(X, W)` itself.  So no ring bridge is needed at any point of this route.

The construction is shorter than the `W.ι` one for the same reason: `hW.fromSpec ≫ f` is *already*
the structure map `Spec.map (algebraMap k Γ(X, W))` on the nose (accepted
`Spec_map_baseToAffineSectionsMap`), so a single `eqToIso` replaces the accepted proof's square, and
no `(restrictionIso g j).symm` hop is required.

Nothing is admitted here.  This module states no sections-level consequence; evaluating this
isomorphism is `AffineDifferentialGammaEquiv`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf KltDP.Geometry.SchemeKaehlerOpenRestriction
open KltDP.Geometry.SchemeModuleRestriction KltDP.Geometry.AffineKaehlerTildeDerivation

universe u

namespace KltDP.Geometry.AffineDifferentialFromSpec

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **The differential sheaf, restricted along the canonical affine chart of an affine open, is the
tilde of the Kähler module of that open's section ring.** -/
def affineDifferentialFromSpecIso {W : X.Opens} (hW : IsAffineOpen W) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    (restriction hW.fromSpec).obj (baseRingSheaf f) ≅
      (differentialModule k Γ(X, W)).tilde := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  have hj : hW.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, W))) := by
    change hW.fromSpec ≫ f = Spec.map (baseToAffineSectionsMap f hW)
    exact (Spec_map_baseToAffineSectionsMap f hW).symm
  exact restrictionIso f hW.fromSpec ≪≫ eqToIso (congrArg baseRingSheaf hj) ≪≫
    AffineKaehlerTildeLocalization.iso k Γ(X, W)

end KltDP.Geometry.AffineDifferentialFromSpec
