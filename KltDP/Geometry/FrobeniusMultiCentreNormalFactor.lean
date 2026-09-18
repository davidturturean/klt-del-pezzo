import KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
import KltDP.Geometry.SemiampleNormalFactor
import KltDP.Examples.FrobeniusMultiCentreNormal

/-!
The original Frobenius multi-centre surface has a normal proper ample
factor. All source hypotheses are supplied by the original constructions:
normality, integrality, projectivity, semiampleness, and eventual complete-
system birationality. The map retains the original field structure, and
the actual ample target line pulls back to a positive power of the
original contracting line.
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

/-- A normal proper ample factor of the original contracting line, with
only the original field, characteristic and distinct-centre hypotheses. -/
theorem normal_proper_ample_factor (hn : 2 < n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    ∃ m : ℕ, 0 < m ∧ ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (CommRingCat.of k)),
      IsProper σ ∧ IsNormalScheme Y ∧ ∃ hY : IsIntegral Y,
        letI : IsIntegral Y := hY
        ∃ π : multiSurface (q + 1) n a ⟶ Y,
          π ≫ σ = multiStructure (q + 1) n a ∧ IsProper π ∧ Surjective π ∧
          IsBirationalScheme π ∧ IsIso π.c ∧
            ∃ A : InvertibleSheaf Y, AmpleSerre.IsAmple A ∧
              Nonempty ((pullbackInvertibleSheaf π A).obj ≅
                (power (originalLine q n a ha) m).obj) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsProper (multiStructure (q + 1) n a) :=
    (originalMultiStructureProjective k (q + 1) n a).isProper
  exact SemiampleNormalFactor.normal_proper_ample_factor
    (multiStructure (q + 1) n a) (originalLine q n a ha)
    (FrobeniusMultiCentreNormal.multiSurface_isNormalScheme (q + 1) n a ha)
    (originalLine_isSemiample q n a ha hn)
    (originalLine_eventuallyBirational q n a ha hn)

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
