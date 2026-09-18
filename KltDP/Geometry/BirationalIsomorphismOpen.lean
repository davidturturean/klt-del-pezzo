import KltDP.Geometry.BirationalAdapters
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# An original birational morphism is an isomorphism over a nonempty open

The inverse of the original generic stalk map spreads out by the pinned
finite-type theorem. Its section is a dominant closed immersion into the
reduced source restriction, hence an isomorphism. No independent function
field comparison or chosen isomorphism open is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry

private theorem isDominant_fromSpecStalk_genericPoint
    (X : Scheme.{u}) [IsIntegral X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff,
    ← (genericPoint_spec X).def]
  exact closure_mono (Set.singleton_subset_iff.mpr
    ⟨IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)),
      Scheme.fromSpecStalk_closedPoint⟩)

private theorem isIso_restrict_of_dominant_section
    {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y) [IsSeparated f]
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

/-- A separated morphism locally of finite type with the original birational
generic stalk map is an isomorphism over an actual nonempty target open. -/
theorem exists_isomorphism_open_of_isBirationalScheme
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsSeparated f]
    (hbir : IsBirationalScheme f) :
    ∃ U : Y.Opens, Nonempty U ∧ IsIso (f ∣_ U) := by
  letI : IsIso (f.stalkMap (genericPoint X)) := hbir.isIso_stalkMap_genericPoint
  let a := inv (Spec.map (f.stalkMap (genericPoint X)))
  let φ : Spec (Y.presheaf.stalk (f.base (genericPoint X))) ⟶ X :=
    a ≫ X.fromSpecStalk (genericPoint X)
  have hφf : φ ≫ f =
      Y.fromSpecStalk (f.base (genericPoint X)) ≫ 𝟙 Y := by
    dsimp only [φ, a]
    rw [Category.assoc, ← Scheme.Spec_map_stalkMap_fromSpecStalk,
      IsIso.inv_hom_id_assoc, Category.comp_id]
  obtain ⟨U, hU, g, hφ, hg⟩ :=
    spread_out_of_isGermInjective' (𝟙 Y) f φ hφf
  letI : IsDominant (X.fromSpecStalk (genericPoint X)) :=
    isDominant_fromSpecStalk_genericPoint X
  letI : IsDominant φ := by dsimp only [φ, a]; infer_instance
  letI : IsDominant
      (U.fromSpecStalkOfMem (f.base (genericPoint X)) hU ≫ g) := by
    rw [← hφ]
    infer_instance
  letI : IsDominant g := IsDominant.of_comp
    (U.fromSpecStalkOfMem (f.base (genericPoint X)) hU) g
  exact ⟨U, ⟨⟨f.base (genericPoint X), hU⟩⟩,
    isIso_restrict_of_dominant_section f U g (by simpa only [Category.comp_id] using hg)⟩

end KltDP.Geometry
