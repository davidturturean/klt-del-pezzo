import KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
import KltDP.Geometry.SemiampleBirationalImage

/-!
# An actual birational projective image of the original Frobenius surface

Projectivity, semiampleness and eventual birationality are supplied by the
proved original-surface producers. The resulting actual morphism is proper
and surjective; an actual ample line on its integral projective target pulls
back to a positive power of the original contracting line.
Normality and the Stein condition are separate remaining target obligations.
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

/-- The original finite-centre surface has an actual proper birational
projective image, without a projectivity or semiampleness premise. -/
theorem exists_integral_projective_birational_image (hn : 2 < n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    ∃ m : ℕ, 0 < m ∧ ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (CommRingCat.of k)),
      IsProjectiveOverField σ ∧ ∃ hY : IsIntegral Y,
        letI : IsIntegral Y := hY
        ∃ π : multiSurface (q + 1) n a ⟶ Y,
          π ≫ σ = multiStructure (q + 1) n a ∧ IsProper π ∧ Surjective π ∧
          IsBirationalScheme π ∧ ∃ A : InvertibleSheaf Y, AmpleSerre.IsAmple A ∧
            Nonempty ((pullbackInvertibleSheaf π A).obj ≅
              (power (originalLine q n a ha) m).obj) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsProper (multiStructure (q + 1) n a) :=
    (originalMultiStructureProjective k (q + 1) n a).isProper
  exact SemiampleProjectiveMap.exists_integral_projective_birational_image
    (multiStructure (q + 1) n a) (originalLine q n a ha)
    (originalLine_isSemiample q n a ha hn) (originalLine_eventuallyBirational q n a ha hn)

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
