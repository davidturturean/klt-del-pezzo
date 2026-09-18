import KltDP.Geometry.FrobeniusTargetDivisorOpen
import KltDP.Geometry.FrobeniusNormalFactorIsomorphism
import KltDP.Geometry.SmoothStructureOnIsomorphismOpen

/-!
The same original target complement is smooth of relative dimension two
and contains the generic point of every target prime curve. Smoothness
is transported through the actual restricted contraction and its original
field triangle, using the already proved smoothness of the original
multicentre surface. No smoothness or canonical data for the target is
assumed.
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

/-- Smoothness on the actual complement follows from its actual map
isomorphism and the original source's relative dimension two. -/
theorem nullImageComplement_smoothTwo (Y : NormalProjectiveSurface k)
    (π : multiSurface (q + 1) n a ⟶ Y.toScheme) [IsProper π]
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    [IsIso (π ∣_ nullImageComplement q n a ha π)] :
    IsSmoothOfRelativeDimension 2
      ((nullImageComplement q n a ha π).ι ≫ Y.structureMorphism) := by
  letI : IsSmoothOfRelativeDimension 2 (multiStructure (q + 1) n a) :=
    multiStructure_smoothTwo (q + 1) n a ha
  exact SmoothStructureOnIsomorphismOpen.isSmoothOfRelativeDimension 2
    (multiStructure (q + 1) n a) Y.structureMorphism π hπ
    (nullImageComplement q n a ha π)

/-- The original normal contraction supplies an actual smooth open
containing every target prime generic point, with no extra target premise. -/
theorem nullImageComplement_smoothTwo_contains_primeGenericPoints
    (hn : 2 < n) (Y : NormalProjectiveSurface k)
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
      IsSmoothOfRelativeDimension 2
        ((nullImageComplement q n a ha π).ι ≫ Y.structureMorphism) ∧
      ∀ C : Y.PrimeCurve, C.genericPoint ∈ nullImageComplement q n a ha π := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  intro hπ hbir hconnected hcriterion
  letI : IsIso (π ∣_ nullImageComplement q n a ha π) :=
    isIso_restrict_nullImageComplement q n a ha hn Y π hπ hbir hconnected hcriterion
  exact ⟨nullImageComplement_smoothTwo q n a ha Y π hπ,
    fun C => genericPoint_mem_nullImageComplement q n a ha hn Y π hcriterion C⟩

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
