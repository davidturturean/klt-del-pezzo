import KltDP.Geometry.ProjectiveLineActualDegreeOne
import KltDP.Geometry.GloballyGeneratedEffectiveCartier
import KltDP.Geometry.CurveDegreeZeroNotBig

/-! The actual homogeneous O(1) generates the original integral Picard
group of P1. Its multiplier is the original Euler degree. The existing
effective-section construction also makes that integer nonnegative for
an actually globally generated line, without a degree assumption. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace KltDP.Geometry.ProjectiveLineIntegralPicardGenerator
open ProjectiveLinePicardExponent ProjectiveLineDegree
open ProjectiveSpaceDegreeOneSheaf ModuleCohomology

variable (k : Type u) [Field k]
local instance generatorLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- The original line's actual Picard class is the degree-th power of
exactly the homogeneous O(1) used by the projective morphism. -/
theorem toPic_eq_degreeOne_zpow (L : InvertibleSheaf (projectiveSpace k 1)) :
    L.toPic = (degreeOne k 1).toPic ^ degree k L := by
  apply hom_injective k
  have hL : hom k L.toPic = Multiplicative.ofAdd (degree k L) := by
    change Multiplicative.ofAdd (value k L.toPic) = Multiplicative.ofAdd (degree k L)
    rw [value_toPic, degree_eq_exponent]
  have h1 : hom k (degreeOne k 1).toPic = Multiplicative.ofAdd (1 : ℤ) := by
    change Multiplicative.ofAdd (value k (degreeOne k 1).toPic) = Multiplicative.ofAdd (1 : ℤ)
    rw [value_toPic, ProjectiveLineActualDegreeOne.exponent_degreeOne]
  rw [map_zpow, hL, h1, ← ofAdd_zsmul, zsmul_eq_mul, mul_one]
  simp only [Int.cast_id]

/-- Actual global generation gives a nonnegative original Euler degree. -/
theorem degree_nonneg_of_globallyGenerated (L : InvertibleSheaf (projectiveSpace k 1))
    (hL : Positivity.IsGloballyGenerated L.obj) : 0 ≤ degree k L := by
  obtain ⟨E, hE, -, ⟨e⟩⟩ :=
    GloballyGeneratedEffectiveCartier.exists_effectiveCartier_avoiding_point
      (projectiveSpace k 1) L hL (genericPoint (projectiveSpace k 1))
  have he := CurveDegreeZeroNotBig.eulerDifference_cartier_eq_effectiveDegree
    (projectiveSpaceToSpec k 1) (ProjectiveLineDegree.dim_le_one k) E hE
  rw [eulerCharacteristic_eq_of_iso (projectiveSpaceToSpec k 1) e] at he
  change 0 ≤ eulerCharacteristic (projectiveSpaceToSpec k 1) L.obj -
    eulerCharacteristic (projectiveSpaceToSpec k 1)
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf)
  rw [he]
  exact Int.natCast_nonneg _

end KltDP.Geometry.ProjectiveLineIntegralPicardGenerator

#check @KltDP.Geometry.ProjectiveLineIntegralPicardGenerator.toPic_eq_degreeOne_zpow
#print axioms KltDP.Geometry.ProjectiveLineIntegralPicardGenerator.degree_nonneg_of_globallyGenerated
