import KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
import KltDP.Geometry.SemiampleNormalPrimeCurveCriterion

/-!
The original Frobenius multi-centre surface has an actual normal proper
ample factor with the exact prime-curve degree criterion. All source
properties and the original contracting line's semiampleness and eventual
birationality are derived. The same source map retains both geometric
and point fiber connectedness and the original positive-power line iso.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusProjectivityProved InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

/-- The same original normal proper factor contracts exactly the original
contracting line's degree-zero prime curves, without new geometric premises. -/
theorem exists_normal_factor_with_prime_criterion (hn : 2 < n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    ∃ m : ℕ, 0 < m ∧ ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (CommRingCat.of k)),
      IsProper σ ∧ IsNormalScheme Y ∧ ∃ hY : IsIntegral Y,
        letI : IsIntegral Y := hY
        ∃ π : multiSurface (q + 1) n a ⟶ Y,
          π ≫ σ = multiStructure (q + 1) n a ∧ IsProper π ∧ Surjective π ∧
          IsBirationalScheme π ∧ IsIso π.c ∧
            (∀ (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ Y),
              ConnectedSpace (pullback π y : Scheme.{u})) ∧
            (∀ y : Y, IsConnected (π.base ⁻¹' {y})) ∧
            ∃ A : InvertibleSheaf Y, AmpleSerre.IsAmple A ∧
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
  exact PrimeCurveImageContraction.exists_normal_factor_with_prime_criterion
    (multiSurfaceSurface (q + 1) n a ha (originalMultiStructureProjective k (q + 1) n a))
    (originalLine q n a ha) (originalLine_isSemiample q n a ha hn)
    (originalLine_eventuallyBirational q n a ha hn)

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
