import KltDP.Geometry.PrimeCurveConstantThroughMono
import KltDP.Geometry.ProjectiveCurveDegreeCriterion
import KltDP.Geometry.AmplePositivity
import KltDP.Geometry.InvertibleSheafSectionPowers

/-!
# Original prime-curve constancy for a projective image of a positive power

The target retains its actual monomorphism into projective space and its
actual degree-one pullback. The positive-power comparison therefore gives
the exact numerical criterion for the original curve map. The proof needs
no properness or birationality of the surface map and no target normality.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.PrimeCurveImageContraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSheafSectionPowers ProjectiveSpaceDegreeOneSheaf

variable {k : Type u} [Field k]
  (X : NormalProjectiveSurface k) (C : X.PrimeCurve)

/-- The actual recursively constructed power has the original multiplied curve degree. -/
theorem restrictionDegree_power (L : InvertibleSheaf X.toScheme) (m : ℕ) :
    C.restrictionDegree (power L m) = (m : ℤ) * C.restrictionDegree L := by
  rw [← C.picardRestrictionDegree_toPic (power L m), power_toPic,
    AmplePositivity.picardRestrictionDegree_pow X C L.toPic m,
    C.picardRestrictionDegree_toPic]

/-- The original map and actual power isomorphism determine its degree-one pullback degree. -/
theorem pullbackDegreeOne_degree_of_iso
    (L : InvertibleSheaf X.toScheme) (m : ℕ) {d : ℕ}
    (g : X.toScheme ⟶ projectiveSpace k d)
    (e : (pullbackInvertibleSheaf g (degreeOne k d)).obj ≅ (power L m).obj) :
    C.restrictionDegree (pullbackInvertibleSheaf g (degreeOne k d)) =
      (m : ℤ) * C.restrictionDegree L :=
  (C.restrictionDegree_eq_of_iso e).trans (restrictionDegree_power X C L m)

variable [IsAlgClosed k]

/-- The actual curve map into a projective image is constant precisely when its
original L-degree is zero, using its actual positive-power degree-one comparison. -/
theorem factors_iff_degree_zero_of_projective_embedding
    (L : InvertibleSheaf X.toScheme) (m : ℕ) (hm : 0 < m)
    {Y : Scheme.{u}} (σ : Y ⟶ Spec (CommRingCat.of k))
    (π : X.toScheme ⟶ Y) (hπ : π ≫ σ = X.structureMorphism)
    {d : ℕ} (i : Y ⟶ projectiveSpace k d) [Mono i]
    (hi : i ≫ projectiveSpaceToSpec k d = σ)
    (e : (pullbackInvertibleSheaf (π ≫ i) (degreeOne k d)).obj ≅ (power L m).obj) :
    (∃ p : Spec (CommRingCat.of k) ⟶ Y,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) ↔
      C.restrictionDegree L = 0 := by
  letI : IsProper C.toSpec := C.toSpec_isProper
  have hgf : (C.inclusion ≫ (π ≫ i)) ≫ projectiveSpaceToSpec k d = C.toSpec := by
    change (C.inclusion ≫ (π ≫ i)) ≫ projectiveSpaceToSpec k d =
      C.inclusion ≫ X.structureMorphism
    simp only [Category.assoc, hi, hπ]
  have hdeg := ProjectiveCurveDegreeCriterion.degree_zero_iff_factors_through_structure
    C.toSpec (le_of_eq C.dimension_one_toScheme) (C.inclusion ≫ (π ≫ i)) hgf
  change C.lineDegree (pullbackInvertibleSheaf
    (C.inclusion ≫ (π ≫ i)) (degreeOne k d)) = 0 ↔ _ at hdeg
  rw [← C.restrictionDegree_pullback (π ≫ i) (degreeOne k d),
    pullbackDegreeOne_degree_of_iso X C L m (π ≫ i) e, mul_eq_zero] at hdeg
  have hm' : (m : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  simp only [hm', false_or] at hdeg
  have hCπ : (C.inclusion ≫ π) ≫ σ = C.toSpec := by
    change (C.inclusion ≫ π) ≫ σ = C.inclusion ≫ X.structureMorphism
    rw [Category.assoc, hπ]
  exact (factors_iff_comp_mono X C (C.inclusion ≫ π) σ hCπ i
    (projectiveSpaceToSpec k d) hi).trans
      (by simpa only [Category.assoc] using hdeg.symm)

/-- The same criterion from the actual image line A and the actual pullback
isomorphism π*A ≅ L^m. The original embedding identifies A with its degree-one pullback. -/
theorem factors_iff_degree_zero_of_imageLine
    (L : InvertibleSheaf X.toScheme) (m : ℕ) (hm : 0 < m)
    {Y : Scheme.{u}} (σ : Y ⟶ Spec (CommRingCat.of k))
    (π : X.toScheme ⟶ Y) (hπ : π ≫ σ = X.structureMorphism)
    {d : ℕ} (i : Y ⟶ projectiveSpace k d) [Mono i]
    (hi : i ≫ projectiveSpaceToSpec k d = σ) (A : InvertibleSheaf Y)
    (eA : (pullbackInvertibleSheaf i (degreeOne k d)).obj ≅ A.obj)
    (eπ : (pullbackInvertibleSheaf π A).obj ≅ (power L m).obj) :
    (∃ p : Spec (CommRingCat.of k) ⟶ Y,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) ↔
      C.restrictionDegree L = 0 :=
  factors_iff_degree_zero_of_projective_embedding X C L m hm σ π hπ i hi
    (((schemeModulePullbackCompIso π i).app (degreeOne k d).obj).symm ≪≫
      (schemeModulePullback π).mapIso eA ≪≫ eπ)

end KltDP.Geometry.PrimeCurveImageContraction
