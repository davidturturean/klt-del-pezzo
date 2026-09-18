import KltDP.Geometry.FrobeniusContractedNoMinusOne
import KltDP.Geometry.ExceptionalCurveFieldPointFactor
import KltDP.Geometry.BirationalAdapters

/-!
The actual original Frobenius contraction is a minimal resolution in the
accepted surface interface. Original smoothness supplies regularity,
original scheme birationality supplies surface birationality, and the
proved exceptional-prime intersection bounds exclude minus-one curves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreExceptionalPrime

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
  (Y : NormalProjectiveSurface k)
  (π : multiSurface (q + 1) n a ⟶ Y.toScheme)
  (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
  (hbir : letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
    IsBirationalScheme π)
  (hlabels : ∀ C : (multiSurfaceSurface (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
    (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
    C = graphPrimeCurve q n a ha (originalMultiStructureProjective k (q + 1) n a) ∨
    (∃ i : Fin n, C = fiberPrimeCurve q n a ha
      (originalMultiStructureProjective k (q + 1) n a) i) ∨
    ∃ (i : Fin n) (j : Fin q), C = exceptionalPrimeCurveSPn q n a ha i (.inl j)
      (originalMultiStructureProjective k (q + 1) n a))

include hn hπ hbir hlabels

/-- The original contraction with its proved prime criterion is a
minimal resolution of its actual normal projective target. -/
theorem isMinimalResolution_of_original_contraction :
    IsMinimalResolution
      (multiSurfaceSurface (q + 1) n a ha
        (originalMultiStructureProjective k (q + 1) n a)) Y π := by
  let X := multiSurfaceSurface (q + 1) n a ha
    (originalMultiStructureProjective k (q + 1) n a)
  have hreg := multiSurfaceSurface_regularPoints (q + 1) n a ha
    (originalMultiStructureProjective k (q + 1) n a)
  have hb : IsBirational (S := X) (X := Y) π :=
    (isBirational_iff_isBirationalScheme (S := X) (X := Y) π).mpr hbir
  refine ⟨⟨hπ, hreg, hb⟩, ?_⟩
  intro C hC hminus
  have hfactor := IsExceptionalCurve.exists_fieldPoint_factor π hπ C hC
  exact contracted_selfIntersectionNumber_ne_neg_one q n a ha hn
    Y.structureMorphism π hlabels C hfactor hminus.selfIntersection

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
