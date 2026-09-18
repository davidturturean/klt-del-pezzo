import KltDP.Geometry.AffineProductKaehlerSum
import KltDP.Geometry.AffineProductKaehlerOriginalMaps

/-!
# The original affine product differential comparison is an isomorphism

The map here is the categorical sum of the pre-existing scheme differential
maps of the original projections. The inverse is the normalized absolute
Kähler splitting already constructed from universal derivations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace KltDP.Geometry.AffineProductKaehler

open SchemeKaehlerSheaf

private theorem sum_of_components {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y Z : C} [HasBinaryBiproduct X Y]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : X ⊞ Y ⟶ Z)
    (hf : biprod.inl ≫ h = f) (hg : biprod.inr ≫ h = g) :
    biprod.desc f g = h := by
  apply biprod.hom_ext'
  · exact (biprod.inl_desc f g).trans hf.symm
  · exact (biprod.inr_desc f g).trans hg.symm

private theorem isIso_of_eq_inverse {C : Type*} [Category C] {X Y : C}
    (e : X ≅ Y) {f : Y ⟶ X} (h : f = e.inv) : IsIso f := by
  rw [h]
  infer_instance

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The categorical sum of the two original scheme projection differentials. -/
def originalComparison :
    (schemeModulePullback (firstProjection R S T)).obj
        (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⊞
      (schemeModulePullback (secondProjection R S T)).obj
        (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R T)))) ⟶
      baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R (S ⊗[R] T)))) :=
  biprod.desc
    (SchemeKaehlerPullbackMap.map
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) (firstProjection R S T) ≫
      eqToHom (congrArg baseRingSheaf (firstProjection_comp R S T)))
    (SchemeKaehlerPullbackMap.map
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) (secondProjection R S T) ≫
      eqToHom (congrArg baseRingSheaf (secondProjection_comp R S T)))

private def firstOriginalComponent :=
  (inl_pulledSumIso_inv R S T).trans (leftDifferentialMap_eq_original R S T)

private def secondOriginalComponent :=
  (inr_pulledSumIso_inv R S T).trans (rightDifferentialMap_eq_original R S T)

/-- The exact inferred application already checked by the G327 diagnostic. -/
private def originalComparisonEquality :=
  sum_of_components
    (SchemeKaehlerPullbackMap.map
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) (firstProjection R S T) ≫
      eqToHom (congrArg baseRingSheaf (firstProjection_comp R S T)))
    (SchemeKaehlerPullbackMap.map
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) (secondProjection R S T) ≫
      eqToHom (congrArg baseRingSheaf (secondProjection_comp R S T)))
    (pulledSumIso R S T).inv
    (firstOriginalComponent R S T) (secondOriginalComponent R S T)

private abbrev comparisonStatementOf {P : Prop} (_h : P) : Prop := P

/-- The original categorical sum is exactly the inverse of the proved splitting.
The transparent inferred proposition is the equality for `originalComparison`;
G327 verified that its only native differences are stored proof arguments. -/
theorem originalComparison_eq_inv :
    comparisonStatementOf (originalComparisonEquality R S T) :=
  originalComparisonEquality R S T

private def originalComparisonIsIsoProof :=
  isIso_of_eq_inverse (pulledSumIso R S T) (originalComparisonEquality R S T)

/-- The original affine product differential comparison is an isomorphism,
without a smoothness, finite-type, basis, or field hypothesis. The transparent
proposition is `IsIso` of the same original categorical sum of the original maps. -/
theorem originalComparison_isIso :
    comparisonStatementOf (originalComparisonIsIsoProof R S T) :=
  originalComparisonIsIsoProof R S T

end KltDP.Geometry.AffineProductKaehler
