import KltDP.Examples.FrobeniusMultiCentreTargetRationalSpan
import KltDP.Geometry.NormalAmpleNumericalRankOne

/-!
The original Frobenius contraction target has numerical Picard rank one.
Its actual ample pullback line spans rational Weil classes by the proved
source Picard generation and contraction relations. Normality injects the
original rational Picard group into those classes, and ampleness supplies
a nonzero original numerical class. Finite dimensionality is also proved.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreTargetPicardRank

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
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
/-- Both clauses concern the original numerical Picard quotient on the
actual target; no source generation or target rank is assumed. -/
theorem picardRank_one :
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
      (hA : AmpleSerre.IsAmple A),
      Y.NumericalSpaceFiniteDimensional ∧ Y.picardRank = 1 := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  intro hπ hbir hconnected hcriterion A m hm e hA
  apply Y.numericalRankOne_of_ample_weilClass_span A hA
  intro c
  exact FrobeniusMultiCentreTargetRationalSpan.rationalWeilClass_eq_smul
    q n a ha π hbir (hπ := hπ) (hcriterion := hcriterion) (hn := hn)
    (hconnected := hconnected) (A := A) (m := m) (hm := hm) (e := e) c

end KltDP.Examples.FrobeniusMultiCentreTargetPicardRank
