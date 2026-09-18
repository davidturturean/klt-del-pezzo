import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! The actual affine rings on an open and its original inverse image
form the original pullback square. The restriction map is retained. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.AffineRestrictionPullbackSquare

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (U : Y.Opens)
  (hU : IsAffineOpen U) (hV : IsAffineOpen (π ⁻¹ᵁ U))

/-- The original restricted morphism has its original affine ring map. -/
theorem restriction_isoSpec :
    (π ∣_ U) ≫ hU.isoSpec.hom = hV.isoSpec.hom ≫ Spec.map (π.app U) := by
  have hh : Spec.map (π.app U) ≫ hU.fromSpec = hV.fromSpec ≫ π := by
    simpa only [Scheme.Hom.appLE_eq_app] using
      IsAffineOpen.Spec_map_appLE_fromSpec π hU hV le_rfl
  rw [← cancel_mono hU.fromSpec]
  calc
    ((π ∣_ U) ≫ hU.isoSpec.hom) ≫ hU.fromSpec = (π ∣_ U) ≫ U.ι := by
      rw [Category.assoc, IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec]
    _ = (π ⁻¹ᵁ U).ι ≫ π := morphismRestrict_ι π U
    _ = (hV.isoSpec.hom ≫ Spec.map (π.app U)) ≫ hU.fromSpec := by
      rw [Category.assoc, hh, ← Category.assoc, IsAffineOpen.isoSpec_hom,
        IsAffineOpen.toSpecΓ_fromSpec]

/-- The two actual affine-chart inclusions preserve the original fiber. -/
theorem isPullback :
    IsPullback hV.fromSpec (Spec.map (π.app U)) π hU.fromSpec := by
  refine (isPullback_morphismRestrict π U).flip.of_iso hV.isoSpec (Iso.refl X)
    hU.isoSpec (Iso.refl Y) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, IsAffineOpen.isoSpec_hom,
      IsAffineOpen.toSpecΓ_fromSpec]
  · exact restriction_isoSpec π U hU hV
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, IsAffineOpen.isoSpec_hom,
      IsAffineOpen.toSpecΓ_fromSpec]

include hU hV in
/-- A surjection of the actual affine restriction rings gives a closed
immersion on the actual open restriction. -/
theorem restriction_isClosedImmersion
    (h : Function.Surjective (π.app U).hom) : IsClosedImmersion (π ∣_ U) := by
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk hV.isoSpec hU.isoSpec (restriction_isoSpec π U hU hV).symm)).mpr
      (IsClosedImmersion.spec_of_surjective (π.app U) h)

#check KltDP.Geometry.AffineRestrictionPullbackSquare.isPullback
#print axioms KltDP.Geometry.AffineRestrictionPullbackSquare.isPullback
#print axioms KltDP.Geometry.AffineRestrictionPullbackSquare.restriction_isClosedImmersion

end KltDP.Geometry.AffineRestrictionPullbackSquare
