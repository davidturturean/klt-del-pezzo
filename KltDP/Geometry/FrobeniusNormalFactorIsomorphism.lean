import KltDP.Geometry.FrobeniusNormalFactorComplement
import KltDP.Geometry.ProperBirationalOffContractedSupport

/-!
The original proper birational Frobenius contraction is an isomorphism
on the actual complement of its null-locus image. The all-prime criterion
and compiled intrinsic null-locus equality supply the generic theorem's
contracted-support condition; no curve-cover or fiber premise is added.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

/-- The actual map is an isomorphism off the actual null-locus image. -/
theorem isIso_restrict_nullImageComplement (hn : 2 < n) (Y : NormalProjectiveSurface k)
    (π : multiSurface (q + 1) n a ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c] :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    ∀ (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
      (hbir : IsBirationalScheme π)
      (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
      (hcriterion : ∀ C : (multiSurfaceSurface (q + 1) n a ha
          (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
        (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
          C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
          C.restrictionDegree (originalLine q n a ha) = 0),
      IsIso (π ∣_ nullImageComplement q n a ha π) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  intro hπ hbir hconnected hcriterion
  let X : NormalProjectiveSurface k := multiSurfaceSurface (q + 1) n a ha
    (originalMultiStructureProjective k (q + 1) n a)
  refine ProperBirationalOffContractedSupport.isIso_restrict X Y π hπ hbir
    (Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha))
    ?_ hconnected (nullImageComplement q n a ha π) ?_
  · intro C hC x hx
    rw [originalNullLocus_eq_curveUnion q n a ha hn]
    exact Set.mem_iUnion₂.mpr ⟨C, (hcriterion C).mp hC, hx⟩
  · intro y hy
    exact hy

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
