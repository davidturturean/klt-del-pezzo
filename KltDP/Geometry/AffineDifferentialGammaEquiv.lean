import KltDP.Geometry.AffineDifferentialFromSpec
import KltDP.Geometry.AffineOpenModuleDenominators
import KltDP.Geometry.AffineModuleGlobalSections
import KltDP.Geometry.AffineTildeGlobalSections

/-!
# The sections of the differential sheaf on an affine open, as Kähler differentials

This is the assembled sections bridge: on an affine open `W` of a `k`-scheme, the sections of
`Ω_{X/k}` over `W` are the Kähler differentials of `Γ(X, W)`, **linearly over `Γ(X, W)` itself**.

* **`gammaSectionsEquiv`**: for any module sheaf `M`, the global sections of `M` restricted along the
  canonical affine chart `hW.fromSpec` are `M`'s sections over `W`, `Γ(X, W)`-linearly.  The
  underlying additive map is the accepted `SchemeModuleRestriction.sectionsOfImageEq` at
  `fromSpec_image_top`, and linearity is the accepted
  `AffineOpenModule.sectionsOfImageEq_base_smul`, whose scalar is a restriction along `W ≤ W` and so
  is the scalar itself.
* **`affineDifferentialGammaEquiv`**:
  `(baseRingSheaf f).val.obj (op W) ≃ₗ[Γ(X, W)] KaehlerDifferential k Γ(X, W)`.

**Both sides carry their own scalars; nothing is transported.**  `(baseRingSheaf f).val.obj (op W)`
is a `ModuleCat Γ(X, W)` by construction and `KaehlerDifferential k Γ(X, W)` is a `Γ(X, W)`-module by
construction, so the statement needs no ring bridge, no `eqToIso`, and no rewriting of an image open.
That is the point of routing through `Spec Γ(X, W)` rather than through the open subscheme
`W.toScheme`: the latter presentation carries scalars from `Γ(W.toScheme, ⊤)`, a ring only
non-reducibly defeq to `Γ(X, W)`, and closing that gap would move a ring and a module together.

The three hops are the chart comparison `AffineDifferentialFromSpec.affineDifferentialFromSpecIso`,
the accepted global-sections functor `AffineModuleTilde.globalSectionsFunctor` (whose object spelling
is `sectionModule _ ⊤` by `rfl`), and `AffineTildeGlobalSections.kaehlerTildeGlobalSectionsEquiv`,
which specialises the accepted unit isomorphism of the tilde adjunction.

Nothing is admitted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf KltDP.Geometry.SchemeModuleRestriction
open KltDP.Geometry.AffineKaehlerTildeDerivation
open KltDP.Geometry.AffineTildeGlobalSections
open KltDP.Geometry.AffineDifferentialFromSpec

universe u

namespace KltDP.Geometry.AffineDifferentialGammaEquiv

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}}

/-- **The global sections of a module sheaf restricted along the canonical affine chart are its
sections over the affine open**, linearly over that open's section ring. -/
def gammaSectionsEquiv (M : X.Modules) {W : X.Opens} (hW : IsAffineOpen W) :
    AffineModuleTilde.sectionModule ((restriction hW.fromSpec).obj M) ⊤ ≃ₗ[Γ(X, W)]
      M.val.obj (op W) := by
  refine AddEquiv.toLinearEquiv
    (sectionsOfImageEq hW.fromSpec M ⊤ W (AffineOpenModule.fromSpec_image_top hW)) ?_
  intro r s
  have hid : X.presheaf.map (homOfLE (le_refl W)).op r = r := by
    change X.presheaf.map (𝟙 (op W)) r = r
    rw [X.presheaf.map_id]
    rfl
  have h := AffineOpenModule.sectionsOfImageEq_base_smul hW M ⊤ W
    (AffineOpenModule.fromSpec_image_top hW) (le_refl W) r s
  rw [hid] at h
  exact h

variable {k : Type u} [CommRing k] (f : X ⟶ Spec (CommRingCat.of k))

/-- **The sections of `Ω_{X/k}` on an affine open are the Kähler differentials of its section
ring**, as `Γ(X, W)`-modules. -/
def affineDifferentialGammaEquiv {W : X.Opens} (hW : IsAffineOpen W) :
    letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
    (baseRingSheaf f).val.obj (op W) ≃ₗ[Γ(X, W)] KaehlerDifferential k Γ(X, W) := by
  letI : Algebra k Γ(X, W) := (baseToAffineSectionsMap f hW).hom.toAlgebra
  exact (gammaSectionsEquiv (baseRingSheaf f) hW).symm ≪≫ₗ
    ((AffineModuleTilde.globalSectionsFunctor Γ(X, W)).mapIso
      (affineDifferentialFromSpecIso f hW)).toLinearEquiv ≪≫ₗ
    (kaehlerTildeGlobalSectionsEquiv k Γ(X, W)).symm

end KltDP.Geometry.AffineDifferentialGammaEquiv
