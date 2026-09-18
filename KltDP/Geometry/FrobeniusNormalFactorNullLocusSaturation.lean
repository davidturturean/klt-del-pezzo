import KltDP.Geometry.NormalFactorNullCurveSaturation
import KltDP.Geometry.FrobeniusMultiCentreBirationalImageNullPrimes
import KltDP.Examples.FrobeniusMultiCentreContractingNullLocus

/-!
The independently defined original Frobenius null locus is saturated
under the same proper birational map with connected fibers and the actual
prime contraction criterion. The exact compiled null-locus/curve-union
comparison is used; no fiber exhaustion or target-dimension assumption
is introduced. Projectivity of the original surface is supplied internally.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreContractingNullLocus

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

/-- An original fiber meeting the actual null locus lies wholly in it.
The map is the given original normal factor, not a newly chosen witness. -/
theorem nullLocus_preimage_image_of_prime_criterion (hn : 2 < n)
    {Y : Scheme.{u}} [IsIntegral Y]
    (σ : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType σ] :
    letI : IsIntegral (multiSurface (q + 1) n a) :=
      multiSurface_isIntegral (q + 1) n a ha
    ∀ (π : multiSurface (q + 1) n a ⟶ Y),
      IsProper π → Surjective π → π ≫ σ = multiStructure (q + 1) n a →
      IsBirationalScheme π → (∀ y : Y, IsConnected (π.base ⁻¹' {y})) →
      (∀ C : (multiSurfaceSurface (q + 1) n a ha
          (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
        (∃ p : Spec (CommRingCat.of k) ⟶ Y,
          C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) ↔
          C.restrictionDegree (originalLine q n a ha) = 0) →
      π.base ⁻¹' (π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
          (originalLine q n a ha)) =
        Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  intro π hproper hsurj hπ hbir hconnected hcriterion
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  let X : NormalProjectiveSurface k := multiSurfaceSurface (q + 1) n a ha
    (originalMultiStructureProjective k (q + 1) n a)
  have hnull : Positivity.nullLocus (multiStructure (q + 1) n a)
      (originalLine q n a ha) =
      ⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree (originalLine q n a ha) = 0},
        (C : Set X.toScheme) :=
    (nullLocus_eq_support q n a ha
      (originalMultiStructureProjective k (q + 1) n a) hn).trans
      (null_curve_union_eq_support q n a ha
        (originalMultiStructureProjective k (q + 1) n a) hn).symm
  rw [hnull]
  exact NormalFactorNullCurveSaturation.preimage_image_null_curve_union
    X (originalLine q n a ha) σ π hπ hbir hconnected hcriterion

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
