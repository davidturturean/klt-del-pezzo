import KltDP.Examples.FrobeniusCharacteristicTwoActualDegree
import KltDP.Examples.FrobeniusMultiCentreCanonicalRetainedPairing

/-!
# The actual characteristic-two canonical adjoint

Transport the already proved integral vector identity through the original
geometric Picard realization. Combine it with the proved class of the
actual anticanonical pullback. The resulting actual adjoint has the class
(n-3)/(n-2) times the original ruling and nonnegative degree on every prime.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusCharacteristicTwoGeometry

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreSemiampleConstruction
open FrobeniusMultiCentreCanonicalWeilRepresentatives
open FrobeniusMultiCentreContractingClass FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusMultiCentrePicardRealization FrobeniusMultiCentreCanonicalRetainedPairing
open FrobeniusMultiCentreCanonicalOpenComparison
open FrobeniusMultiCentreRulingNef InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

local instance adjointPrimeTwo : Fact (1 + 1).Prime := ⟨Nat.prime_two⟩

variable (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

/-- The actual integral M and original canonical line class satisfy the
existing lattice identity after applying the proved geometric realization. -/
theorem contractingClass_add_multiCanonicalClass :
    contractingClass 1 n a ha + multiCanonicalClass 2 n a ha =
      ((n : ℤ) - 3) • multiSecondFiberClass 2 n a := by
  rw [contractingClass_eq_realization,
    multiCanonicalClass_eq_realization 1 n a ha, ← map_add,
    FrobeniusCharacteristicTwo.nef_add_canonical, map_zsmul,
    FrobeniusMultiCentreRealizedCurveClasses.realization_secondFiber]

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

/-- The actual divisor L + K_S/(n-2) has the stated original ruling class. -/
theorem anticanonicalPullback_adjoint :
    (surface n a ha).rationalWeilToRationalPicard
        (multiSurfaceSurface_regularPoints 2 n a ha (originalMultiStructureProjective k 2 n a))
        (anticanonicalPullback n a ha hn Y π hπ hbir hconnected hcriterion A m hm e +
          (1 / ((n : ℚ) - 2)) • (surface n a ha).rationalCartierToWeilHom
            (canonicalCartier 1 n a ha (originalMultiStructureProjective k 2 n a))) =
      (((n : ℚ) - 3) / ((n : ℚ) - 2)) • (surface n a ha).picardTensorInclusion
        (multiSecondFiberClass 2 n a) := by
  rw [map_add, map_smul, rationalWeilToRationalPicard_cartier,
    anticanonicalPullback_picard, canonicalCartier_picard, ← smul_add, ← map_add,
    contractingClass_add_multiCanonicalClass, map_zsmul,
    ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
  congr 1
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_ofNat, one_div, div_eq_mul_inv]
  ring

/-- The actual adjoint is nef in the original universal prime-degree test. -/
theorem anticanonicalPullback_adjoint_degree_nonneg (C : (surface n a ha).PrimeCurve) :
    0 ≤ (surface n a ha).rationalPicardRestrictionDegree C
      ((surface n a ha).rationalWeilToRationalPicard
        (multiSurfaceSurface_regularPoints 2 n a ha (originalMultiStructureProjective k 2 n a))
        (anticanonicalPullback n a ha hn Y π hπ hbir hconnected hcriterion A m hm e +
          (1 / ((n : ℚ) - 2)) • (surface n a ha).rationalCartierToWeilHom
            (canonicalCartier 1 n a ha (originalMultiStructureProjective k 2 n a)))) := by
  rw [anticanonicalPullback_adjoint, map_smul, rationalPicardRestrictionDegree_inclusion]
  change 0 ≤ (((n : ℚ) - 3) / ((n : ℚ) - 2)) *
    ((surface n a ha).picardRestrictionDegreeHom C (multiSecondFiberClass 2 n a) : ℚ)
  have hdegree := secondRuling_primeDegree_nonneg 2 n a ha
    (originalMultiStructureProjective k 2 n a) C
  have hdegreeQ : (0 : ℚ) ≤
      ((surface n a ha).picardRestrictionDegreeHom C (multiSecondFiberClass 2 n a) : ℚ) := by
    exact_mod_cast hdegree
  have hnQ : (3 : ℚ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  exact mul_nonneg (div_nonneg (sub_nonneg.mpr hnQ) (by linarith)) hdegreeQ

end KltDP.Examples.FrobeniusCharacteristicTwoGeometry

#print axioms KltDP.Examples.FrobeniusCharacteristicTwoGeometry.anticanonicalPullback_adjoint
#print axioms KltDP.Examples.FrobeniusCharacteristicTwoGeometry.anticanonicalPullback_adjoint_degree_nonneg
