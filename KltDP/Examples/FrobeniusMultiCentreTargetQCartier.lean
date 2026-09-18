import KltDP.Examples.FrobeniusMultiCentreTargetCanonicalRelation
import KltDP.Geometry.QCartierFromPicardClass

/-!
# The actual Frobenius contraction target has a Q-Cartier canonical divisor

The canonical divisor is constructed independently from top differentials on
the target's smooth large open. Its proved integral class relation with the
original pulled-back line gives an actual positive Cartier multiple. The
coefficient is positive for every positive power and n > 2, in every admitted
characteristic; no sign restriction on d or ampleness premise is needed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreTargetQCartier

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
/-- The original positive-power contraction witness gives Q-Cartierness of
the independently constructed target canonical Weil divisor. -/
theorem targetCanonicalWeil_qCartier :
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
      (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj),
      Y.QCartier (rationalizeWeilDivisor Y
        (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  intro hπ hbir hconnected hcriterion A m hm e
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hp' : (0 : ℤ) < (q + 1 : ℕ) := by exact_mod_cast Nat.succ_pos q
  have hn' : (2 : ℤ) < n := by exact_mod_cast hn
  apply Y.qCartier_of_positive_int_picard_relation
    (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)
    ((m : ℤ) * (q + 1 : ℕ) * ((n : ℤ) - 2))
    (mul_pos (mul_pos hm' hp') (sub_pos.mpr hn')) A.toPic
    (2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2))
  exact FrobeniusMultiCentreTargetCanonicalRelation.canonical_relation
    q n a ha hn Y π hπ hbir hconnected hcriterion A m e

end KltDP.Examples.FrobeniusMultiCentreTargetQCartier
