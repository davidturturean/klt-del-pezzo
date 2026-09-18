import KltDP.Geometry.RationalWeilCartierRestrictionDegree
import KltDP.Geometry.PrimeCurveRestrictionKernelPairing
import KltDP.Examples.FrobeniusTargetCanonicalPullbackClass
import KltDP.Examples.FrobeniusMultiCentreTargetQCartier
import KltDP.Geometry.ExceptionalCurveFieldPointFactor
import KltDP.Geometry.ExceptionalCurveOfFieldPointFactor

/-!
# The actual characteristic-two anticanonical pullback and its shortest degree

The divisor below is the negative of the actual pullback of the original
target canonical Weil divisor. The original canonical relation proves its
class is M/(n-2); this is not an input. Integral nef degrees and the actual
contraction criterion bound every exterior prime, and the original newest
exceptional curves attain the bound.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusCharacteristicTwoGeometry

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreSemiampleConstruction
open FrobeniusMultiCentreCanonicalWeilRepresentatives
open FrobeniusMultiCentreContractingClass FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalPrime
open PrimeCurveClassPairing InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

local instance primeTwo : Fact (1 + 1).Prime := ⟨Nat.prime_two⟩

/-- The original two-step-per-centre surface, with its original projectivity proof. -/
abbrev surface (n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    NormalProjectiveSurface k :=
  sourceSurface 1 n a ha (originalMultiStructureProjective k 2 n a)

variable (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

private theorem originalLine_class :
    Additive.ofMul (originalLine 1 n a ha).toPic = contractingClass 1 n a ha :=
  contractingLine_class 1 n a ha (originalMultiStructureProjective k 2 n a)

/-- The integer degree of the original M on each original last exceptional prime is one. -/
theorem originalLine_newest_degree (i : Fin n) :
    (exceptionalPrimeCurveSPn 1 n a ha i (.inr PUnit.unit)
      (originalMultiStructureProjective k 2 n a)).restrictionDegree
        (originalLine 1 n a ha) = 1 := by
  let S := surface n a ha
  let P := exceptionalPrimeCurveSPn 1 n a ha i (.inr PUnit.unit)
    (originalMultiStructureProjective k 2 n a)
  letI := exceptionalCurve_isIntegral 1 n a ha i (.inr PUnit.unit)
  have hdegree := restrictionDegree_eq_pairing_kernel_right S
    (multiSurfaceSurface_regularPoints 2 n a ha (originalMultiStructureProjective k 2 n a))
    P (exceptionalCurveι 1 n a i (.inr PUnit.unit))
    (coe_exceptionalPrimeCurveSPn 1 n a ha i (.inr PUnit.unit)
      (originalMultiStructureProjective k 2 n a))
    (FrobeniusMultiCentreExceptionalGlobalClasses.exceptionalKernelLine 1 n a ha i (.inr PUnit.unit)) rfl
    (originalLine 1 n a ha) (contractingClass 1 n a ha) (originalLine_class n a ha)
  exact hdegree.trans (contractingClass_newest_pairing 1 n a ha
    (originalMultiStructureProjective k 2 n a) i)

variable (hn : 2 < n) (Y : NormalProjectiveSurface k)
    (π : (surface n a ha).toScheme ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c]
    (hπ : π ≫ Y.structureMorphism = multiStructure 2 n a)
    (hbir : IsBirationalScheme π)
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (hcriterion : ∀ C : (surface n a ha).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine 1 n a ha) = 0)
    (A : InvertibleSheaf Y.toScheme) (m : ℕ) (hm : 0 < m)
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine 1 n a ha) m).obj)

/-- The negative of the original target canonical pullback, using its proved Q-Cartier witness. -/
def anticanonicalPullback : (surface n a ha).RationalWeilDivisor := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  exact -QCartierPullback.pullback π
    (rationalizeWeilDivisor Y
      (targetCanonicalWeil 1 n a ha hn Y π hπ hbir hconnected hcriterion))
    (FrobeniusMultiCentreTargetQCartier.targetCanonicalWeil_qCartier
      1 n a ha hn Y π hπ hbir hconnected hcriterion A m hm e)

/-- The actual canonical pullback has class M/(n-2), by the original canonical relation. -/
theorem anticanonicalPullback_class :
    (surface n a ha).rationalWeilClassMap
        (anticanonicalPullback n a ha hn Y π hπ hbir hconnected hcriterion A m hm e) =
      (1 / ((n : ℚ) - 2)) • (surface n a ha).rationalWeilClassMap
        ((surface n a ha).rationalCartierToWeilHom
          (contractingDivisor 1 n a ha (originalMultiStructureProjective k 2 n a))) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let S := surface n a ha
  let KX := targetCanonicalWeil 1 n a ha hn Y π hπ hbir hconnected hcriterion
  let hK := FrobeniusMultiCentreTargetQCartier.targetCanonicalWeil_qCartier
    1 n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
  have h := FrobeniusTargetCanonicalPullbackClass.target_canonical_pullback_class
    1 n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hK
  have h' : S.rationalWeilClassMap
      (QCartierPullback.pullback π (rationalizeWeilDivisor Y KX) hK) =
      (-(2 : ℚ) / (2 * ((n : ℚ) - 2))) • S.rationalWeilClassMap
        (S.rationalCartierToWeilHom
          (contractingDivisor 1 n a ha (originalMultiStructureProjective k 2 n a))) := by
    simpa only [Nat.reduceAdd, Int.cast_mul, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast, Nat.cast_ofNat,
      sub_self, zero_mul, sub_zero, contractingWeil] using h
  change S.rationalWeilClassMap
    (-QCartierPullback.pullback π (rationalizeWeilDivisor Y KX) hK) = _
  rw [map_neg, h', ← neg_smul]
  have hd : (n : ℚ) - 2 ≠ 0 :=
    ne_of_gt (FrobeniusCharacteristicTwo.parameter_denominator_pos (by omega))
  have hc : -(-(2 : ℚ) / (2 * ((n : ℚ) - 2))) = 1 / ((n : ℚ) - 2) := by
    field_simp [hd]
  rw [hc]

/-- The original rational Picard class of the actual anticanonical pullback. -/
theorem anticanonicalPullback_picard :
    (surface n a ha).rationalWeilToRationalPicard
        (multiSurfaceSurface_regularPoints 2 n a ha (originalMultiStructureProjective k 2 n a))
        (anticanonicalPullback n a ha hn Y π hπ hbir hconnected hcriterion A m hm e) =
      (1 / ((n : ℚ) - 2)) • (surface n a ha).picardTensorInclusion
        (contractingClass 1 n a ha) := by
  have h := (surface n a ha).rationalWeilToRationalPicard_of_class_eq_smul_cartier
    (multiSurfaceSurface_regularPoints 2 n a ha (originalMultiStructureProjective k 2 n a))
    _ (contractingDivisor 1 n a ha (originalMultiStructureProjective k 2 n a)) _
    (anticanonicalPullback_class n a ha hn Y π hπ hbir hconnected hcriterion A m hm e)
  simpa only [contractingDivisor_class] using h

/-- Degree on an original prime curve, through the established Weil-to-Picard comparison. -/
def anticanonicalDegree (C : (surface n a ha).PrimeCurve) : ℚ :=
  (surface n a ha).rationalPicardRestrictionDegree C
    ((surface n a ha).rationalWeilToRationalPicard
      (multiSurfaceSurface_regularPoints 2 n a ha (originalMultiStructureProjective k 2 n a))
      (anticanonicalPullback n a ha hn Y π hπ hbir hconnected hcriterion A m hm e))

/-- The actual degree is the proved rational scalar times the original integral M-degree. -/
theorem anticanonicalDegree_eq (C : (surface n a ha).PrimeCurve) :
    anticanonicalDegree n a ha hn Y π hπ hbir hconnected hcriterion A m hm e C =
      (1 / ((n : ℚ) - 2)) * (C.restrictionDegree (originalLine 1 n a ha) : ℚ) :=
  (surface n a ha).rationalRestrictionDegree_of_class_eq_smul_cartier
    (multiSurfaceSurface_regularPoints 2 n a ha (originalMultiStructureProjective k 2 n a))
    _ (contractingDivisor 1 n a ha (originalMultiStructureProjective k 2 n a)) _
    (anticanonicalPullback_class n a ha hn Y π hπ hbir hconnected hcriterion A m hm e) C

/-- Every exterior prime on the original surface has degree at least 1/(n-2). -/
theorem exterior_anticanonicalDegree_lower_bound (C : (surface n a ha).PrimeCurve)
    (hC : ¬ IsExceptionalCurve π C) :
    1 / ((n : ℚ) - 2) ≤
      anticanonicalDegree n a ha hn Y π hπ hbir hconnected hcriterion A m hm e C := by
  have hnonneg := contractingClass_degree_nonneg 1 n a ha
    (originalMultiStructureProjective k 2 n a) (Nat.le_of_lt hn) C
  rw [← originalLine_class n a ha] at hnonneg
  change 0 ≤ C.picardRestrictionDegree (originalLine 1 n a ha).toPic at hnonneg
  rw [C.picardRestrictionDegree_toPic] at hnonneg
  have hne : C.restrictionDegree (originalLine 1 n a ha) ≠ 0 := by
    intro hz
    obtain ⟨p, hp, _⟩ := (hcriterion C).mpr hz
    exact hC (IsExceptionalCurve.of_fieldPoint_factor π C p hp)
  have hone : 1 ≤ C.restrictionDegree (originalLine 1 n a ha) := by omega
  have honeQ : (1 : ℚ) ≤ (C.restrictionDegree (originalLine 1 n a ha) : ℚ) := by
    exact_mod_cast hone
  rw [anticanonicalDegree_eq]
  have hscale : 0 ≤ 1 / ((n : ℚ) - 2) :=
    le_of_lt (FrobeniusCharacteristicTwo.exteriorDegree_pos (by omega))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left honeQ hscale

include hπ hcriterion in
/-- Each original newest exceptional curve is exterior for this same contraction. -/
theorem newest_not_exceptional (i : Fin n) :
    ¬ IsExceptionalCurve π (exceptionalPrimeCurveSPn 1 n a ha i (.inr PUnit.unit)
      (originalMultiStructureProjective k 2 n a)) := by
  intro hC
  have hzero := (hcriterion _).mp
    (IsExceptionalCurve.exists_fieldPoint_factor π hπ _ hC)
  rw [originalLine_newest_degree n a ha i] at hzero
  norm_num at hzero

/-- Each original newest exceptional curve attains the universal exterior lower bound. -/
theorem newest_anticanonicalDegree (i : Fin n) :
    anticanonicalDegree n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
      (exceptionalPrimeCurveSPn 1 n a ha i (.inr PUnit.unit)
        (originalMultiStructureProjective k 2 n a)) = 1 / ((n : ℚ) - 2) := by
  rw [anticanonicalDegree_eq, originalLine_newest_degree]
  norm_num

end KltDP.Examples.FrobeniusCharacteristicTwoGeometry

#print axioms KltDP.Examples.FrobeniusCharacteristicTwoGeometry.anticanonicalPullback_class
#print axioms KltDP.Examples.FrobeniusCharacteristicTwoGeometry.exterior_anticanonicalDegree_lower_bound
#print axioms KltDP.Examples.FrobeniusCharacteristicTwoGeometry.newest_anticanonicalDegree
