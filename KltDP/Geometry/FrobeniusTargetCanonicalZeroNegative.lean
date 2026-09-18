import KltDP.Examples.FrobeniusMultiCentreTargetCanonicalRelation
import KltDP.Geometry.WeilCanonicalSignRelation

/-!
# The actual zero and negative Frobenius canonical cases

The original same-target relation retains its positive multiplier
m*p*(n-2). At coefficient zero it yields rational linear triviality of
the original canonical divisor. At negative coefficient it produces an
actual ample Cartier numerator of that same canonical divisor.
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

private theorem canonical_multiplier_pos (q n m : ℕ) (hn : 2 < n) (hm : 0 < m) :
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

include hn hproper hsurj hc hπ hbir hconnected hcriterion hm e

/-- At d=0, the original target canonical Weil divisor is Q-linearly trivial. -/
theorem targetCanonicalWeil_qLinearlyEquivalent_zero
    (hd : 2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2) = 0) :
    Y.QLinearlyEquivalent (rationalizeWeilDivisor Y
      (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) 0 := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  let KX := targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion
  have hrel := FrobeniusMultiCentreTargetCanonicalRelation.canonical_relation
    q n a ha hn Y π hπ hbir hconnected hcriterion A m e
  have hzero : ((m : ℤ) * (q + 1 : ℕ) * ((n : ℤ) - 2)) • Y.weilClassMap KX = 0 := by
    simpa only [hd, zero_zsmul, add_zero] using hrel
  exact Y.qLinearlyEquivalent_zero_of_nonzero_zsmul_class_eq_zero KX
    ((m : ℤ) * (q + 1 : ℕ) * ((n : ℤ) - 2))
    (ne_of_gt (canonical_multiplier_pos q n m hn hm)) hzero

/-- At d<0, the original target canonical divisor is Q-ample, via an
actual ample Cartier multiple derived from the same original line A. -/
theorem targetCanonicalWeil_qAmple (hA : AmpleSerre.IsAmple A)
    (hd : 2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2) < 0) :
    Y.QAmple (rationalizeWeilDivisor Y
      (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  apply Y.qAmple_of_negative_canonical_relation
    (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion) A
    ((m : ℤ) * (q + 1 : ℕ) * ((n : ℤ) - 2))
    (2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2))
    (canonical_multiplier_pos q n m hn hm) hd hA
  exact FrobeniusMultiCentreTargetCanonicalRelation.canonical_relation
    q n a ha hn Y π hπ hbir hconnected hcriterion A m e

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
