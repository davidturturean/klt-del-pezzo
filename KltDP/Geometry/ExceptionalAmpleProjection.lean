import KltDP.Geometry.ActualExceptionalStieltjes
import KltDP.Geometry.AmpleSelfIntersectionPositive
import KltDP.Geometry.RationalHodgeIndex

/-!
# Orthogonal projection of an ample class away from actual contracted curves

The coefficients are the inverse of the negative original intersection matrix
applied to the original curve degrees. No matrix positivity, coefficient sign,
degree vanishing, or positive-square witness is supplied to the ample consumer.
The construction takes place in the original rationalized Picard group.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory Matrix
open scoped BigOperators
universe u v

namespace KltDP.Geometry.ExceptionalAmpleProjection

open NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (S : NormalProjectiveSurface k)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
  {I : Type v} [Fintype I] (C : I → S.PrimeCurve)

/-- The original integral sheaf class in the existing rational Picard group. -/
def lineClass (H : InvertibleSheaf S.toScheme) : S.RationalPicard :=
  S.picardTensorInclusion (Additive.ofMul H.toPic)

/-- The literal inverse-matrix coefficients for any original rational class. -/
def coefficients (z : S.RationalPicard) : I → ℚ := by
  classical
  exact (-NullCurveIntersectionMatrix.intersectionMatrix S hregular C)⁻¹ *ᵥ
    (fun i => S.rationalPicardRestrictionDegree (C i) z)

/-- Add the original prime Cartier classes with their inverse-matrix coefficients. -/
def projectedClass (z : S.RationalPicard) : S.RationalPicard :=
  z + ∑ i, coefficients S hregular C z i • S.primeCurveRationalPicardClass hregular (C i)

@[simp]
theorem degree_lineClass (H : InvertibleSheaf S.toScheme) (E : S.PrimeCurve) :
    S.rationalPicardRestrictionDegree E (lineClass S H) = (E.restrictionDegree H : ℚ) := by
  rw [lineClass, S.rationalPicardRestrictionDegree_inclusion]
  exact congrArg (fun n : ℤ => (n : ℚ)) (E.picardRestrictionDegree_toPic H)

theorem degree_primeClass (E F : S.PrimeCurve) :
    S.rationalPicardRestrictionDegree E (S.primeCurveRationalPicardClass hregular F) =
      (S.intersectionPairing hregular (S.primeCurveCartier hregular E)
        (S.primeCurveCartier hregular F) : ℚ) := by
  unfold NormalProjectiveSurface.primeCurveRationalPicardClass
  rw [S.rationalPicardRestrictionDegree_inclusion]
  change (E.picardRestrictionDegree
    (cartierPicardClass S.toScheme (S.primeCurveCartier hregular F)) : ℚ) = _
  rw [← E.intersectionNumber_eq_picardRestrictionDegree,
    PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber]

theorem degree_projectedClass (z : S.RationalPicard) (E : S.PrimeCurve) :
    S.rationalPicardRestrictionDegree E (projectedClass S hregular C z) =
      S.rationalPicardRestrictionDegree E z +
        ∑ i, coefficients S hregular C z i *
          (S.intersectionPairing hregular (S.primeCurveCartier hregular E)
            (S.primeCurveCartier hregular (C i)) : ℚ) := by
  simp only [projectedClass, map_add, map_sum, map_smul, smul_eq_mul,
    degree_primeClass]

variable {X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hbir : IsBirationalScheme π) (hinj : Function.Injective C)
  (hcontracted : ∀ i, IsExceptionalCurve π (C i))

include hπ hbir hinj hcontracted in
theorem matrix_mul_coefficients (z : S.RationalPicard) :
    (-NullCurveIntersectionMatrix.intersectionMatrix S hregular C) *ᵥ
        coefficients S hregular C z =
      (fun i => S.rationalPicardRestrictionDegree (C i) z) := by
  classical
  let A := -NullCurveIntersectionMatrix.intersectionMatrix S hregular C
  letI : Invertible A := (KltDP.LinearAlgebra.isUnit_of_posDef
    (ActualExceptionalStieltjes.negativeIntersectionMatrix_posDef
      π hπ hbir hregular C hinj hcontracted)).invertible
  change A *ᵥ (A⁻¹ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

include hπ hbir hinj hcontracted in
theorem degree_projectedClass_family (z : S.RationalPicard) (i : I) :
    S.rationalPicardRestrictionDegree (C i) (projectedClass S hregular C z) = 0 := by
  classical
  have hrow := congrFun (matrix_mul_coefficients S hregular C π hπ hbir hinj hcontracted z) i
  rw [degree_projectedClass]
  have hsum : (∑ j, coefficients S hregular C z j *
      (S.intersectionPairing hregular (S.primeCurveCartier hregular (C i))
        (S.primeCurveCartier hregular (C j)) : ℚ)) =
      (NullCurveIntersectionMatrix.intersectionMatrix S hregular C *ᵥ
        coefficients S hregular C z) i := by
    simp only [Matrix.mulVec, dotProduct,
      NullCurveIntersectionMatrix.intersectionMatrix, mul_comm]
  rw [hsum]
  simp only [Matrix.neg_mulVec, Pi.neg_apply] at hrow
  linarith

include hπ hbir hinj hcontracted in
theorem coefficients_pos (H : InvertibleSheaf S.toScheme) (hH : AmpleSerre.IsAmple H)
    (i : I) : 0 < coefficients S hregular C (lineClass S H) i := by
  classical
  apply KltDP.LinearAlgebra.stieltjes_inverse_mulVec_positive
    (ActualExceptionalStieltjes.negativeIntersectionMatrix_posDef
      π hπ hbir hregular C hinj hcontracted)
    (ActualExceptionalStieltjes.negativeIntersectionMatrix_offDiagonal hregular C hinj)
    (b := fun j => S.rationalPicardRestrictionDegree (C j) (lineClass S H)) _ i
  intro j
  change 0 < S.rationalPicardRestrictionDegree (C j) (lineClass S H)
  rw [degree_lineClass]
  exact_mod_cast AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple S H hH (C j)

include hπ hbir hinj hcontracted in
theorem degree_projectedClass_pos_of_not_mem (H : InvertibleSheaf S.toScheme)
    (hH : AmpleSerre.IsAmple H) (E : S.PrimeCurve) (hE : E ∉ Set.range C) :
    0 < S.rationalPicardRestrictionDegree E
      (projectedClass S hregular C (lineClass S H)) := by
  rw [degree_projectedClass, degree_lineClass]
  have hpos : (0 : ℚ) < E.restrictionDegree H := by
    exact_mod_cast AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple S H hH E
  apply add_pos_of_pos_of_nonneg hpos
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg
  · exact (coefficients_pos S hregular C π hπ hbir hinj hcontracted H hH i).le
  · exact_mod_cast PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg
      S hregular E (C i) (fun he => hE ⟨i, he.symm⟩)

include hπ hbir hinj hcontracted in
theorem degree_projectedClass_eq_zero_iff (H : InvertibleSheaf S.toScheme)
    (hH : AmpleSerre.IsAmple H) (E : S.PrimeCurve) :
    S.rationalPicardRestrictionDegree E
      (projectedClass S hregular C (lineClass S H)) = 0 ↔ E ∈ Set.range C := by
  constructor
  · intro hz
    by_contra hE
    exact (ne_of_gt (degree_projectedClass_pos_of_not_mem
      S hregular C π hπ hbir hinj hcontracted H hH E hE)) hz
  · rintro ⟨i, rfl⟩
    exact degree_projectedClass_family S hregular C π hπ hbir hinj hcontracted _ i

include hπ hbir hinj hcontracted in
theorem degree_projectedClass_nonneg (H : InvertibleSheaf S.toScheme)
    (hH : AmpleSerre.IsAmple H) (E : S.PrimeCurve) :
    0 ≤ S.rationalPicardRestrictionDegree E
      (projectedClass S hregular C (lineClass S H)) := by
  by_cases hE : E ∈ Set.range C
  · rw [(degree_projectedClass_eq_zero_iff
      S hregular C π hπ hbir hinj hcontracted H hH E).mpr hE]
  · exact (degree_projectedClass_pos_of_not_mem
      S hregular C π hπ hbir hinj hcontracted H hH E hE).le

include hπ hbir hinj hcontracted in
theorem square_projectedClass (H : InvertibleSheaf S.toScheme) :
    S.rationalPicardIntersectionBilinForm hregular
        (projectedClass S hregular C (lineClass S H))
        (projectedClass S hregular C (lineClass S H)) =
      (S.selfIntersection hregular H : ℚ) +
        ∑ i, coefficients S hregular C (lineClass S H) i * (C i).restrictionDegree H := by
  let z := projectedClass S hregular C (lineClass S H)
  have hzero (i : I) : S.rationalPicardIntersectionBilinForm hregular z
      (S.primeCurveRationalPicardClass hregular (C i)) = 0 := by
    rw [S.rationalPicardIntersectionBilinForm_primeCurve]
    exact degree_projectedClass_family S hregular C π hπ hbir hinj hcontracted _ i
  have hz : S.rationalPicardIntersectionBilinForm hregular z z =
      S.rationalPicardIntersectionBilinForm hregular z (lineClass S H) := by
    change S.rationalPicardIntersectionBilinForm hregular z
      (lineClass S H + ∑ i, coefficients S hregular C (lineClass S H) i •
        S.primeCurveRationalPicardClass hregular (C i)) = _
    simp only [map_add, map_sum, map_smul, hzero,
      smul_zero, Finset.sum_const_zero, add_zero]
  have hsymm : S.rationalPicardIntersectionBilinForm hregular z (lineClass S H) =
      S.rationalPicardIntersectionBilinForm hregular (lineClass S H) z :=
    S.rationalPicardIntersectionBilinForm_isSymm hregular z (lineClass S H)
  rw [hz, hsymm]
  change S.rationalPicardIntersectionBilinForm hregular (lineClass S H)
    (lineClass S H + ∑ i, coefficients S hregular C (lineClass S H) i •
      S.primeCurveRationalPicardClass hregular (C i)) = _
  rw [map_add, map_sum]
  simp only [map_smul, S.rationalPicardIntersectionBilinForm_primeCurve,
    degree_lineClass, smul_eq_mul]
  congr 1
  exact S.rationalPicardIntersectionBilinForm_inclusion hregular
    (Additive.ofMul H.toPic) (Additive.ofMul H.toPic)

include hπ hbir hinj hcontracted in
theorem square_projectedClass_pos (H : InvertibleSheaf S.toScheme)
    (hH : AmpleSerre.IsAmple H) :
    0 < S.rationalPicardIntersectionBilinForm hregular
      (projectedClass S hregular C (lineClass S H))
      (projectedClass S hregular C (lineClass S H)) := by
  rw [square_projectedClass S hregular C π hπ hbir hinj hcontracted]
  apply add_pos_of_pos_of_nonneg
  · exact_mod_cast AmpleSelfIntersectionPositive.selfIntersection_pos_of_isAmple S hregular H hH
  · apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · exact (coefficients_pos S hregular C π hπ hbir hinj hcontracted H hH i).le
    · exact_mod_cast (AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple
        S H hH (C i)).le

end KltDP.Geometry.ExceptionalAmpleProjection

#check @KltDP.Geometry.ExceptionalAmpleProjection.degree_projectedClass_eq_zero_iff
#check @KltDP.Geometry.ExceptionalAmpleProjection.square_projectedClass_pos
#print axioms KltDP.Geometry.ExceptionalAmpleProjection.coefficients_pos
#print axioms KltDP.Geometry.ExceptionalAmpleProjection.degree_projectedClass_eq_zero_iff
#print axioms KltDP.Geometry.ExceptionalAmpleProjection.square_projectedClass_pos
