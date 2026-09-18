import KltDP.Examples.FrobeniusMultiCentreTargetCanonicalRelation
import KltDP.Geometry.AmpleCartierFromWeilClass

/-!
The original canonical relation and the ample line of the actual normal
contraction produce an ample Cartier multiple of its anticanonical Weil
divisor whenever the explicit coefficient d is positive. The positive
power m is retained in the Cartier multiple.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreTargetAnticanonicalAmple

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreCanonicalWeilRepresentatives
open KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
open InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k)
    (π : multiSurface (q + 1) n a ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c]

include hn in
/-- The original target anticanonical divisor has an actual positive
ample Cartier multiple when its explicit coefficient is positive. -/
theorem exists_ample_anticanonical_multiple :
    letI : IsIntegral (multiSurface (q + 1) n a) :=
      multiSurface_isIntegral (q + 1) n a ha
    ∀ (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
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
      (hd : (0 : ℤ) < 2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2)),
      ∃ N : ℕ, 0 < N ∧ ∃ B : CartierDivisor Y.toScheme,
        Y.cartierToWeilHom B = N •
          (-(targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) ∧
        AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf Y.toScheme B) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  intro hπ hbir hconnected hcriterion A m hm e hA hd
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hp' : (0 : ℤ) < (q + 1 : ℕ) := by exact_mod_cast Nat.succ_pos q
  have hn' : (2 : ℤ) < n := by exact_mod_cast hn
  apply Y.exists_ample_anticanonical_multiple_of_positive_relation
    (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion) A
    ((m : ℤ) * (q + 1 : ℕ) * ((n : ℤ) - 2))
    (2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2))
    (mul_pos (mul_pos hm' hp') (sub_pos.mpr hn')) hd hA
  exact FrobeniusMultiCentreTargetCanonicalRelation.canonical_relation
    q n a ha hn Y π hπ hbir hconnected hcriterion A m e

end KltDP.Examples.FrobeniusMultiCentreTargetAnticanonicalAmple
