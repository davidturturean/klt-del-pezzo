import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Original dominant sections over an open

This public adapter retains the construction already checked in the private
helpers of `BirationalIsomorphismOpen`: the actual restriction pullback
turns a dominant section into a surjective closed immersion. The original
source needs only to be reduced for that section to be an isomorphism.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.DominantOpenSection

/-- The canonical map from the original generic stalk is dominant. -/
theorem fromSpecStalk_genericPoint_isDominant
    (X : Scheme.{u}) [IsIntegral X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff,
    ← (genericPoint_spec X).def]
  exact closure_mono (Set.singleton_subset_iff.mpr
    ⟨IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)),
      Scheme.fromSpecStalk_closedPoint⟩)

/-- A dominant section of the original separated morphism over an open
makes the original restricted morphism an isomorphism. -/
theorem isIso_restrict_of_dominant_section
    {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) [IsSeparated f]
    (U : Y.Opens) (g : U.toScheme ⟶ X) [IsDominant g]
    (hg : g ≫ f = U.ι) : IsIso (f ∣_ U) := by
  let hP := isPullback_morphismRestrict f U
  let s : U.toScheme ⟶ (f ⁻¹ᵁ U).toScheme :=
    hP.lift (𝟙 _) g (by simpa only [Category.id_comp] using hg.symm)
  have hs : s ≫ (f ∣_ U) = 𝟙 _ := hP.lift_fst _ _ _
  have hsι : s ≫ (f ⁻¹ᵁ U).ι = g := hP.lift_snd _ _ _
  letI : IsSeparated (f ∣_ U) := IsLocalAtTarget.restrict (P := @IsSeparated) inferInstance U
  letI : IsClosedImmersion (s ≫ (f ∣_ U)) := by rw [hs]; infer_instance
  letI : IsClosedImmersion s := IsClosedImmersion.of_comp s (f ∣_ U)
  letI : IsDominant (s ≫ (f ⁻¹ᵁ U).ι) := by rw [hsι]; infer_instance
  letI : IsDominant s := IsDominant.of_comp_of_isOpenImmersion s (f ⁻¹ᵁ U).ι
  letI : Surjective s :=
    surjective_of_isDominant_of_isClosed_range s IsClosedImmersion.base_closed.2
  letI : IsReduced (f ⁻¹ᵁ U).toScheme := isReduced_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  letI : IsIso s := isIso_of_isClosedImmersion_of_surjective s
  letI : IsIso (s ≫ (f ∣_ U)) := by rw [hs]; infer_instance
  exact IsIso.of_isIso_comp_left s (f ∣_ U)

end KltDP.Geometry.DominantOpenSection
