import KltDP.Geometry.AmpleCanonicalRelationConverse
import KltDP.Geometry.FrobeniusTargetAnticanonicalQAmple
import KltDP.Examples.FrobeniusMultiCentreTargetCanonicalRelation
import KltDP.Examples.FrobeniusArithmetic

/-!
# The exact anticanonical ample cases for the original Frobenius target

The converse uses the original target canonical relation and an actual
ample Cartier numerator of its negative. The forward implication is the
proved positive-case construction. Both directions retain the same
target, contraction, canonical representative, ample line and exponent.
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

private theorem ample_converse_multiplier_pos (q n m : ℕ) (hn : 2 < n) (hm : 0 < m) :
    (0 : ℤ) < (m : ℤ) * (q + 1 : ℕ) * ((n : ℤ) - 2) := by
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hpZ : (0 : ℤ) < (q + 1 : ℕ) := by exact_mod_cast Nat.succ_pos q
  have hnZ : (2 : ℤ) < n := by exact_mod_cast hn
  exact mul_pos (mul_pos hmZ hpZ) (sub_pos.mpr hnZ)

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

/-- Q-ampleness of the actual target anticanonical divisor forces d>0. -/
theorem targetCanonicalWeil_coefficient_pos_of_neg_qAmple
    (hQ : Y.QAmple (-rationalizeWeilDivisor Y
      (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion))) :
    (0 : ℤ) < 2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  apply Y.canonical_coefficient_pos_of_neg_qAmple
    (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion) A
    ((m : ℤ) * (q + 1 : ℕ) * ((n : ℤ) - 2))
    (2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2))
    (ample_converse_multiplier_pos q n m hn hm) hA ?_ hQ
  exact FrobeniusMultiCentreTargetCanonicalRelation.canonical_relation
    q n a ha hn Y π hπ hbir hconnected hcriterion A m e

/-- The same actual target anticanonical divisor is Q-ample exactly when
the original integer coefficient is positive. -/
theorem targetCanonicalWeil_neg_qAmple_iff :
    Y.QAmple (-rationalizeWeilDivisor Y
      (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) ↔
      (0 : ℤ) < 2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2) := by
  exact ⟨targetCanonicalWeil_coefficient_pos_of_neg_qAmple
      q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hA,
    targetCanonicalWeil_neg_qAmple
      q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hA⟩

/-- For the original prime p=q+1 and n>2, negative K is Q-ample exactly
for p=2 or for p=3,n=3. No contraction witness is replaced. -/
theorem targetCanonicalWeil_neg_qAmple_iff_parameters :
    Y.QAmple (-rationalizeWeilDivisor Y
      (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) ↔
      q + 1 = 2 ∨ (q + 1 = 3 ∧ n = 3) := by
  have hp : (q + 1).Prime := Fact.out
  have hn3 : 3 ≤ n := by omega
  exact (targetCanonicalWeil_neg_qAmple_iff
    q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hA).trans
      (FrobeniusArithmetic.integerNumerator_pos_iff hp hn3)

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
