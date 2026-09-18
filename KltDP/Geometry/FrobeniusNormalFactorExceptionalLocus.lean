import KltDP.Geometry.FrobeniusNormalFactorIsomorphism
import KltDP.Geometry.ExceptionalCurveOfFieldPointFactor

/-!
# The actual exceptional locus is the original Frobenius null locus

The accepted resolution exceptional locus is identified using the original
isomorphism complement and the actual point factorizations of null primes.
No regularity or singularity assertion for their target images is required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

/-- The accepted exceptional locus of the original normal contraction equals
the independently defined null locus of the original line. -/
theorem exceptionalLocus_eq_originalNullLocus (hn : 2 < n)
    (Y : NormalProjectiveSurface k)
    (π : multiSurface (q + 1) n a ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c] :
    letI : IsIntegral (multiSurface (q + 1) n a) :=
      multiSurface_isIntegral (q + 1) n a ha
    ∀ (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
      (hbir : IsBirationalScheme π)
      (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
      (hcriterion : ∀ C : (multiSurfaceSurface (q + 1) n a ha
          (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
        (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
          C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
          C.restrictionDegree (originalLine q n a ha) = 0),
      KltDP.Geometry.exceptionalLocus
          (S := multiSurfaceSurface (q + 1) n a ha
            (originalMultiStructureProjective k (q + 1) n a)) (X := Y) π =
        Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  intro hπ hbir hconnected hcriterion
  let S := multiSurfaceSurface (q + 1) n a ha
    (originalMultiStructureProjective k (q + 1) n a)
  letI : IsIso (π ∣_ nullImageComplement q n a ha π) :=
    isIso_restrict_nullImageComplement q n a ha hn Y π hπ hbir hconnected hcriterion
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxnull
    have hxU : x ∈ π ⁻¹ᵁ nullImageComplement q n a ha π := by
      rw [preimage_nullImageComplement q n a ha hn Y π hπ hbir hconnected hcriterion]
      exact hxnull
    exact hx ⟨nullImageComplement q n a ha π, hxU, inferInstance⟩
  · intro x hx
    rw [originalNullLocus_eq_curveUnion q n a ha hn] at hx
    obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨p, hp, _⟩ := (hcriterion C).mpr hC
    exact IsExceptionalCurve.subset_exceptionalLocus (S := S) (X := Y) π
      (IsExceptionalCurve.of_fieldPoint_factor (X := S) (Y := Y) π C p hp) hxC

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
