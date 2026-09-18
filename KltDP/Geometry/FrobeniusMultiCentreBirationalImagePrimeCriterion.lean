import KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
import KltDP.Geometry.SemiampleImagePrimeCurveCriterion

/-!
The actual original Frobenius surface has a proper surjective birational
projective image with an ample line pulling back to a positive power of
its original contracting line. The same morphism contracts exactly the
original prime curves of degree zero against that line. All projectivity,
semiampleness and eventual birationality inputs are supplied by the original
surface producers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusProjectivityProved InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

/-- The same actual birational image contracts exactly the original line's degree-zero primes. -/
theorem exists_birational_image_with_prime_criterion (hn : 2 < n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    ∃ m : ℕ, 0 < m ∧ ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (CommRingCat.of k)),
      IsProjectiveOverField σ ∧ ∃ hY : IsIntegral Y,
        letI : IsIntegral Y := hY
        ∃ π : multiSurface (q + 1) n a ⟶ Y,
          π ≫ σ = multiStructure (q + 1) n a ∧ IsProper π ∧ Surjective π ∧
          IsBirationalScheme π ∧ ∃ A : InvertibleSheaf Y, AmpleSerre.IsAmple A ∧
            Nonempty ((pullbackInvertibleSheaf π A).obj ≅
              (power (originalLine q n a ha) m).obj) ∧
            ∀ C : (multiSurfaceSurface (q + 1) n a ha
                (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
              (∃ p : Spec (CommRingCat.of k) ⟶ Y,
                C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) ↔
              C.restrictionDegree (originalLine q n a ha) = 0 := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsProper (multiStructure (q + 1) n a) :=
    (originalMultiStructureProjective k (q + 1) n a).isProper
  exact PrimeCurveImageContraction.exists_birational_image_with_prime_criterion
    (multiSurfaceSurface (q + 1) n a ha (originalMultiStructureProjective k (q + 1) n a))
    (originalLine q n a ha) (originalLine_isSemiample q n a ha hn)
    (originalLine_eventuallyBirational q n a ha hn)

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
