import KltDP.Examples.FrobeniusCharacteristicTwoActualDegree

/-! The exact least degree in the set of all original exterior-prime degrees. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusCharacteristicTwoGeometry

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusProjectivityProved
open FrobeniusMultiCentreSemiampleConstruction FrobeniusMultiCentreExceptionalPrime
open InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

local instance minimumPrimeTwo : Fact (1 + 1).Prime := ⟨Nat.prime_two⟩

/-- The original actual anticanonical pullback has exact least exterior
degree 1/(n-2), with an actual original prime attaining it. -/
theorem anticanonicalDegree_isLeast_exterior
    (n : ℕ) (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k) (π : (surface n a ha).toScheme ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c]
    (hπ : π ≫ Y.structureMorphism = multiStructure 2 n a)
    (hbir : IsBirationalScheme π)
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (hcriterion : ∀ C : (surface n a ha).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine 1 n a ha) = 0)
    (A : InvertibleSheaf Y.toScheme) (m : ℕ) (hm : 0 < m)
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine 1 n a ha) m).obj) :
    IsLeast {d : ℚ | ∃ C : (surface n a ha).PrimeCurve,
      ¬ IsExceptionalCurve π C ∧
        d = anticanonicalDegree n a ha hn Y π hπ hbir hconnected hcriterion A m hm e C}
      (1 / ((n : ℚ) - 2)) := by
  let i : Fin n := ⟨0, by omega⟩
  let P := exceptionalPrimeCurveSPn 1 n a ha i (.inr PUnit.unit)
    (originalMultiStructureProjective k 2 n a)
  have hP : ¬ IsExceptionalCurve π P :=
    newest_not_exceptional (n := n) (a := a) (ha := ha) (Y := Y) (π := π)
      (hπ := hπ) (hcriterion := hcriterion) i
  refine ⟨⟨P, hP, ?_⟩, ?_⟩
  · exact (newest_anticanonicalDegree n a ha hn Y π hπ hbir
      hconnected hcriterion A m hm e i).symm
  · intro d hd
    obtain ⟨C, hC, rfl⟩ := hd
    exact exterior_anticanonicalDegree_lower_bound n a ha hn Y π hπ hbir
      hconnected hcriterion A m hm e C hC

end KltDP.Examples.FrobeniusCharacteristicTwoGeometry

#print axioms KltDP.Examples.FrobeniusCharacteristicTwoGeometry.anticanonicalDegree_isLeast_exterior
