import KltDP.Examples.ProjectiveLineProductPicardCoordinates
import KltDP.Geometry.RationalHodgeIndex
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The actual numerical Picard rank of the product is two

The coordinate maps are the original horizontal and vertical curve degrees.
Surjectivity uses the proved integral-multiple representation of every
original numerical class, followed by the actual integral ruling equivalence.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
universe u

namespace KltDP.Examples.ProjectiveLineProductNumericalRank

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusStageZeroProjective
open FrobeniusGraphPicardClassFiberClasses FrobeniusRulingClassPairing
open ProjectiveLineProductPicardGeneration

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- These are the two original prime-curve degree tests on the original quotient. -/
def rulingNumericalCoordinates :
    (projectiveProductSurface (k := k)).NumericalClassGroup →ₗ[ℚ] ℚ × ℚ :=
  ((projectiveProductSurface (k := k)).numericalRestrictionDegree
    (horizontalPrimeCurve (0 : k))).prod
    ((projectiveProductSurface (k := k)).numericalRestrictionDegree
      (verticalPrimeCurve (0 : k)))

theorem coordinates_integral (p : Additive (projectiveProduct k).Pic) :
    rulingNumericalCoordinates ((projectiveProductSurface (k := k)).picardNumericalMap p) =
      (((rulingCoordinates p).1 : ℚ), ((rulingCoordinates p).2 : ℚ)) := by
  apply Prod.ext
  · exact (projectiveProductSurface (k := k)).numericalRestrictionDegree_picardNumericalMap
      (horizontalPrimeCurve (0 : k)) p
  · exact (projectiveProductSurface (k := k)).numericalRestrictionDegree_picardNumericalMap
      (verticalPrimeCurve (0 : k)) p

theorem coordinates_ruling_integral (x : ℤ × ℤ) :
    rulingNumericalCoordinates ((projectiveProductSurface (k := k)).picardNumericalMap
      (rulingPicardEquiv x)) = ((x.1 : ℚ), (x.2 : ℚ)) := by
  rw [coordinates_integral]
  have hx : rulingCoordinates (rulingPicardEquiv (k := k) x) = x :=
    rulingCoordinates_rulingClassHom x
  rw [hx]

/-- The original two integral rulings, now with rational coefficients. -/
def rulingNumericalHom : (ℚ × ℚ) →ₗ[ℚ]
    (projectiveProductSurface (k := k)).NumericalClassGroup where
  toFun x :=
    x.1 • (projectiveProductSurface (k := k)).picardNumericalMap
      (rulingPicardEquiv (1, 0)) +
    x.2 • (projectiveProductSurface (k := k)).picardNumericalMap
      (rulingPicardEquiv (0, 1))
  map_add' x y := by
    change (x.1 + y.1) • _ + (x.2 + y.2) • _ = _
    simp only [add_smul]
    abel
  map_smul' a x := by
    change (a * x.1) • _ + (a * x.2) • _ = a • (_ + _)
    rw [smul_add, smul_smul, smul_smul]

theorem coordinates_rulingNumericalHom (x : ℚ × ℚ) :
    rulingNumericalCoordinates (rulingNumericalHom (k := k) x) = x := by
  change rulingNumericalCoordinates (x.1 • _ + x.2 • _) = _
  rw [map_add, map_smul, map_smul, coordinates_ruling_integral,
    coordinates_ruling_integral]
  ext <;> simp [smul_eq_mul]

theorem rulingNumericalHom_integral (x : ℤ × ℤ) :
    rulingNumericalHom (k := k) ((x.1 : ℚ), (x.2 : ℚ)) =
      (projectiveProductSurface (k := k)).picardNumericalMap (rulingPicardEquiv x) := by
  rcases x with ⟨x, y⟩
  change (x : ℚ) • (projectiveProductSurface (k := k)).picardNumericalMap
      (rulingPicardEquiv (1, 0)) +
    (y : ℚ) • (projectiveProductSurface (k := k)).picardNumericalMap
      (rulingPicardEquiv (0, 1)) =
    (projectiveProductSurface (k := k)).picardNumericalMap (rulingPicardEquiv (x, y))
  simp only [rulingPicardEquiv_apply, one_zsmul, zero_zsmul, add_zero, zero_add,
    map_add, map_zsmul, Int.cast_smul_eq_zsmul]

theorem rulingNumericalHom_surjective :
    Function.Surjective (rulingNumericalHom (k := k)) := by
  intro c
  obtain ⟨n, hn, p, hp⟩ :=
    (projectiveProductSurface (k := k)).numericalClass_exists_positive_integral_multiple c
  obtain ⟨x, hx⟩ := (rulingPicardEquiv (k := k)).surjective p
  have hclass : rulingNumericalHom (k := k) ((x.1 : ℚ), (x.2 : ℚ)) = (n : ℚ) • c := by
    rw [rulingNumericalHom_integral, hx]
    exact hp
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  refine ⟨(n : ℚ)⁻¹ • ((x.1 : ℚ), (x.2 : ℚ)), ?_⟩
  rw [map_smul, hclass, smul_smul, inv_mul_cancel₀ hnq, one_smul]

/-- An equivalence with the original numerical quotient, not a replacement space. -/
def rulingNumericalEquiv : (ℚ × ℚ) ≃ₗ[ℚ]
    (projectiveProductSurface (k := k)).NumericalClassGroup :=
  LinearEquiv.ofBijective rulingNumericalHom
    ⟨(show Function.LeftInverse rulingNumericalCoordinates
      (rulingNumericalHom (k := k)) from coordinates_rulingNumericalHom).injective,
      rulingNumericalHom_surjective⟩

theorem picardRank_eq_two : (projectiveProductSurface (k := k)).picardRank = 2 := by
  change Module.finrank ℚ (projectiveProductSurface (k := k)).NumericalClassGroup = 2
  rw [← (rulingNumericalEquiv (k := k)).finrank_eq, Module.finrank_prod]
  norm_num

end KltDP.Examples.ProjectiveLineProductNumericalRank

#check @KltDP.Examples.ProjectiveLineProductNumericalRank.rulingNumericalEquiv
#check @KltDP.Examples.ProjectiveLineProductNumericalRank.picardRank_eq_two
#print axioms KltDP.Examples.ProjectiveLineProductNumericalRank.picardRank_eq_two
