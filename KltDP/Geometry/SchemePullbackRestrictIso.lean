import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Restrictions of base changes of morphisms that are isomorphisms over an open

Two small generic facts about schemes, used to glue several point-blowup towers into one
surface by fibre products.

* If `g : T ⟶ X` is an isomorphism over an open `U` (i.e. `g ∣_ U` is an isomorphism), then the
  base change `pullback.fst f g : S ×_X T ⟶ S` is an isomorphism over `f ⁻¹ᵁ U`. The proof pastes
  the two accepted pullback squares of the restriction and of the fibre product, and compares with
  the base change of `g ∣_ U` along `f ∣_ U`, which is an isomorphism because isomorphisms are
  stable under base change.
* `g ∣_ U` is an isomorphism exactly when the pullback projection `pullback.snd g U.ι` is, by the
  pinned definition of the restriction.

Only pinned Mathlib is used; no scheme, isomorphism or restriction property is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Geometry

variable {S T X : Scheme.{u}}

/-- The pullback projection onto an open is an isomorphism when the restriction is. -/
theorem isIso_pullback_snd_ι_of_restrict (g : T ⟶ X) (U : X.Opens) [IsIso (g ∣_ U)] :
    IsIso (pullback.snd g U.ι) := by
  have h : pullback.snd g U.ι = (pullbackRestrictIsoRestrict g U).hom ≫ (g ∣_ U) := by
    change pullback.snd g U.ι =
      (pullbackRestrictIsoRestrict g U).hom ≫
        ((pullbackRestrictIsoRestrict g U).inv ≫ pullback.snd g U.ι)
    rw [Iso.hom_inv_id_assoc]
  rw [h]
  infer_instance

/-- The base change of a morphism that is an isomorphism over `U` is an isomorphism over the
preimage of `U`. -/
theorem isIso_pullback_fst_restrict (f : S ⟶ X) (g : T ⟶ X) (U : X.Opens) [IsIso (g ∣_ U)] :
    IsIso (pullback.fst f g ∣_ (f ⁻¹ᵁ U)) := by
  have h12 : IsPullback (pullback.fst f g ∣_ (f ⁻¹ᵁ U))
      ((pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ pullback.snd f g)
      ((f ⁻¹ᵁ U).ι ≫ f) g :=
    (isPullback_morphismRestrict (pullback.fst f g) (f ⁻¹ᵁ U)).paste_vert
      (IsPullback.of_hasPullback f g)
  have h34 : IsPullback (pullback.fst (f ∣_ U) (g ∣_ U))
      (pullback.snd (f ∣_ U) (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι)
      ((f ∣_ U) ≫ U.ι) g :=
    ((IsPullback.of_hasPullback (f ∣_ U) (g ∣_ U)).flip.paste_horiz
      (isPullback_morphismRestrict g U).flip).flip
  rw [morphismRestrict_ι] at h34
  have he : pullback.fst f g ∣_ (f ⁻¹ᵁ U) =
      (h12.isoIsPullback _ _ h34).hom ≫ pullback.fst (f ∣_ U) (g ∣_ U) :=
    (h12.isoIsPullback_hom_fst _ _ h34).symm
  rw [he]
  infer_instance

end KltDP.Geometry
