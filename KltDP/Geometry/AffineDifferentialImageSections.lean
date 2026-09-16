import KltDP.Geometry.AffineDifferentialGamma
import KltDP.Geometry.AffineOpenModuleDenominators

/-!
# The restricted differential sections, over the affine open itself

The sections bridge needs the sections of `Ω_{X/k}` restricted to an affine open `W`, read over `W`
rather than over the image `W.ι ''ᵁ ⊤`.  The obvious route — asserting a `ModuleCat`-level equality —
is **wrong**, and was disproved by build (record `20260912T042522Z-693727`): the sheaf-level
`restriction` is `PresheafOfModules.pushforward φ = pushforward₀ F R ⋙ restrictScalars φ`
(pinned `Presheaf/Pushforward.lean:70`), so the bare `ModuleCat.of _ (M.obj _)` shape is only the inner
factor and the `restrictScalars` wrapper blocks `rfl`.  Both sides have the same carrier; an equality of
`ModuleCat` objects is simply the wrong request.

The accepted tree already has the right shape.  `SchemeModuleRestriction.sectionsOfImageEq` takes the
open equality as a **hypothesis of the definition** and `subst`s it, staying at `.val.presheaf.obj`
(additive sections) where the accepted `restrictionSectionsIso` lives.  That avoids transporting a
bundled ring-and-module pair, which is the heterogeneous transport the lane rules forbid.

* **`differentialImageSections`**: that instantiation for the differential sheaf —
  `((restriction W.ι).obj (baseRingSheaf f)).val.presheaf.obj (op ⊤) ≃+ (baseRingSheaf f).val.presheaf.obj (op W)`,
  via `Scheme.Opens.ι_image_top`.

This is the additive half of the last hop.  Linearity is deliberately **not** claimed here: the two
sides carry scalars from `Γ(W.toScheme, ⊤)` and `Γ(X, W)` respectively, rings that pinned Mathlib calls
only "non-reducibly defeq" and bridges with the `eqToIso`-based `Scheme.Opens.topIso`
(`AffineDifferentialSectionsGamma.sectionsRingIso`).  Adding linearity over that bridge is the next
step, not this one.

Nothing is admitted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf KltDP.Geometry.SchemeModuleRestriction

universe u

namespace KltDP.Geometry.AffineDifferentialImageSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **The restricted differential sections, read over the affine open itself.**  The open equality is a
hypothesis that is `subst`-ed inside the accepted `sectionsOfImageEq`, not a transport. -/
def differentialImageSections (W : X.Opens) :
    ((restriction W.ι).obj (baseRingSheaf f)).val.presheaf.obj (op (⊤ : W.toScheme.Opens)) ≃+
      (baseRingSheaf f).val.presheaf.obj (op W) :=
  sectionsOfImageEq W.ι (baseRingSheaf f) ⊤ W W.ι_image_top

end KltDP.Geometry.AffineDifferentialImageSections
