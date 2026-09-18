import KltDP.Examples.FrobeniusMultiCentreTargetAnticanonicalAmple
import KltDP.Geometry.QAmpleIntegralMultiple

/-!
# Q-ampleness of the actual Frobenius target anticanonical divisor

The positive coefficient gives an actual ample Cartier multiple through
the original integral canonical relation. Rationalizing that exact divisor
equality proves Q-ampleness of the same independent target canonical Weil
representative. The original ample line and positive exponent are retained.
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

/-- Every original positive-power contraction has Q-ample negative
canonical divisor when the original integer coefficient d is positive. -/
theorem targetCanonicalWeil_neg_qAmple
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k)
    (π : (sourceSurface q n a ha
      (originalMultiStructureProjective k (q + 1) n a)).toScheme ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c]
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
    (hd : (0 : ℤ) < 2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2)) :
    Y.QAmple (-rationalizeWeilDivisor Y
      (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨N, hN, B, hB, hBample⟩ :=
    FrobeniusMultiCentreTargetAnticanonicalAmple.exists_ample_anticanonical_multiple
      q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hA hd
  have hq := Y.qAmple_of_ample_integral_multiple
    (-(targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion))
    N hN B hB hBample
  simpa only [map_neg] using hq

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
