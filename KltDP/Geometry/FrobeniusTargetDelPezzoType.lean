import KltDP.Geometry.FrobeniusNormalProjectiveSurfaceKlt
import KltDP.Geometry.FrobeniusTargetAnticanonicalQAmple
import KltDP.Geometry.DelPezzoType

/-!
# The original positive Frobenius target is a klt del Pezzo surface

The universal all-normal-model KLT theorem and the actual ample Cartier
multiple use the same target canonical divisor. Boundary zero therefore
gives the original klt del Pezzo and del Pezzo-type predicates.
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
    (hd : (0 : ℤ) < 2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2))

include hn hproper hsurj hc hπ hbir hconnected hcriterion hm e hA hd

/-- Every original positive-coefficient contraction is klt del Pezzo,
using its independently constructed canonical divisor and boundary zero. -/
theorem target_isKltDelPezzo : IsKltDelPezzo Y := by
  apply (isLogDelPezzoPair_zero_iff Y).mpr
  refine ⟨targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion, ?_, ?_⟩
  · exact targetCanonicalWeil_isKltWithCanonicalDivisor
      q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
  · exact targetCanonicalWeil_neg_qAmple
      q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hA hd

/-- The same original target is of del Pezzo type, with effective boundary zero. -/
theorem target_isDelPezzoType : IsDelPezzoType Y :=
  isDelPezzoType_of_isKltDelPezzo Y
    (target_isKltDelPezzo q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hA hd)

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
