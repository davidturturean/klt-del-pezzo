import KltDP.Geometry.KltDelPezzoCanonicalInvariant
import KltDP.Geometry.FrobeniusNormalProjectiveSurfaceKlt
import KltDP.Geometry.FrobeniusTargetAnticanonicalAmpleIff

/-!
# The intrinsic klt del Pezzo classification of the same Frobenius target

The target's original all-normal-model KLT theorem and the exact
anticanonical ampleness classification are combined through canonical
representative independence. The conclusion uses the intrinsic surface
predicate, with no chosen canonical divisor appearing in it.
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

/-- The original target is intrinsically klt del Pezzo exactly when d>0. -/
theorem target_isKltDelPezzo_iff :
    IsKltDelPezzo Y ↔
      (0 : ℤ) < 2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2) := by
  have hklt := targetCanonicalWeil_isKltWithCanonicalDivisor
    q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
  exact (isKltDelPezzo_iff_neg_qAmple_of_isKltWithCanonicalDivisor Y
    (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion) hklt).trans
      (targetCanonicalWeil_neg_qAmple_iff
        q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hA)

/-- For the original prime p=q+1 and n>2, the same target is intrinsically
klt del Pezzo exactly for p=2 or for p=3,n=3. -/
theorem target_isKltDelPezzo_iff_parameters :
    IsKltDelPezzo Y ↔ q + 1 = 2 ∨ (q + 1 = 3 ∧ n = 3) := by
  have hp : (q + 1).Prime := Fact.out
  have hn3 : 3 ≤ n := by omega
  exact (target_isKltDelPezzo_iff
    q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hA).trans
      (FrobeniusArithmetic.integerNumerator_pos_iff hp hn3)

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
