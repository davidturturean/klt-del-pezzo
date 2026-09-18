import KltDP.Geometry.FrobeniusTargetCanonicalZeroNegative
import KltDP.Geometry.FrobeniusTargetAnticanonicalQAmple
import KltDP.Examples.FrobeniusArithmetic

/-!
# Actual Frobenius canonical sign cases for the original prime parameters

The already proved arithmetic trichotomy is applied to the actual same
target canonical divisor. Positive parameters give Q-ample negative K;
the unique zero case gives Q-linear triviality; the remaining parameters
give Q-ample K. The original exponent and ample pullback line are kept.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved InvertibleSheafSectionPowers NormalProjectiveSurface
open FrobeniusMultiCentreCanonicalWeilRepresentatives

local instance {k : Type u} [Field k] (T : NormalProjectiveSurface k) :
    IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k)
    (π : (sourceSurface q n a ha
      (originalMultiStructureProjective k (q + 1) n a)).toScheme ⟶ Y.toScheme)
    [hproper : IsProper π] [hsurj : Surjective π] [hc : IsIso π.c]
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hbir : IsBirationalScheme π)
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (hcriterion : ∀ C : (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine q n a ha) = 0)
    (A : InvertibleSheaf Y.toScheme) (m : ℕ) (hm : 0 < m)
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj)
    (hA : AmpleSerre.IsAmple A)

include hn hproper hsurj hc hπ hbir hconnected hcriterion hm e hA

/-- The full prime-parameter sign trichotomy concerns the same original
canonical representative and the actual ampleness/linear-equivalence predicates. -/
theorem targetCanonicalWeil_parameter_sign_cases :
    let KX := targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion
    let D := rationalizeWeilDivisor Y KX
    ((q + 1 = 2 ∨ (q + 1 = 3 ∧ n = 3)) ∧ Y.QAmple (-D)) ∨
      ((q + 1 = 3 ∧ n = 4) ∧ Y.QLinearlyEquivalent D 0) ∨
      ((q + 1 ≠ 2 ∧ (q + 1 ≠ 3 ∨ 5 ≤ n)) ∧ Y.QAmple D) := by
  have hp : (q + 1).Prime := Fact.out
  have hn3 : 3 ≤ n := by omega
  rcases lt_trichotomy (0 : ℤ) (FrobeniusArithmetic.integerNumerator (q + 1) n) with
    hpos | hzero | hneg
  · refine Or.inl ⟨(FrobeniusArithmetic.integerNumerator_pos_iff hp hn3).mp hpos, ?_⟩
    exact targetCanonicalWeil_neg_qAmple
      q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hA hpos
  · refine Or.inr (Or.inl
      ⟨(FrobeniusArithmetic.integerNumerator_eq_zero_iff hp hn3).mp hzero.symm, ?_⟩)
    exact targetCanonicalWeil_qLinearlyEquivalent_zero
      q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hzero.symm
  · refine Or.inr (Or.inr
      ⟨(FrobeniusArithmetic.integerNumerator_neg_iff hp hn3).mp hneg, ?_⟩)
    exact targetCanonicalWeil_qAmple
      q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hA hneg

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
