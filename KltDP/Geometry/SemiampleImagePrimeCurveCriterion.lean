import KltDP.Geometry.GeneratedImagePrimeCurveCriterion
import KltDP.Geometry.SemiampleLargePower

/-!
# An actual semiample birational image with its exact prime-curve criterion

The original generated complete-system image supplies the proper
surjective birational map and ample target line. The original curve
criterion is retained in the existential conclusion before the explicit
image and projective embedding are hidden.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.PrimeCurveImageContraction

open CompleteLinearSystemMap InvertibleSheafSectionPowers

/-- A semiample eventually birational line on the original surface gives
an actual proper birational projective image contracting exactly its degree-zero primes. -/
theorem exists_birational_image_with_prime_criterion
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (L : InvertibleSheaf X.toScheme)
    (hsemi : Positivity.IsSemiample L)
    (hevent : KeelCompleteSystem.EventuallyBirational X.structureMorphism L) :
    ∃ m : ℕ, 0 < m ∧ ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (CommRingCat.of k)),
      IsProjectiveOverField σ ∧ ∃ hY : IsIntegral Y,
        letI : IsIntegral Y := hY
        ∃ π : X.toScheme ⟶ Y, π ≫ σ = X.structureMorphism ∧
          IsProper π ∧ Surjective π ∧ IsBirationalScheme π ∧
          ∃ A : InvertibleSheaf Y, AmpleSerre.IsAmple A ∧
            Nonempty ((pullbackInvertibleSheaf π A).obj ≅ (power L m).obj) ∧
            ∀ C : X.PrimeCurve,
              (∃ p : Spec (CommRingCat.of k) ⟶ Y,
                C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) ↔
              C.restrictionDegree L = 0 := by
  obtain ⟨N, _, hN⟩ := hevent
  obtain ⟨m, hm, hmN, hG⟩ :=
    SemiampleActualPowers.exists_globallyGenerated_power_ge L hsemi N
  obtain ⟨hpos, hbir⟩ := hN m hmN
  refine ⟨m, hm,
    SchematicImageGlued.image (morphism X.structureMorphism (power L m) hpos),
    imageStructure X.structureMorphism (power L m) hpos,
    imageStructure_isProjective X.structureMorphism (power L m) hpos,
    image_isIntegral X.structureMorphism (power L m) hpos,
    generatedToImage X.structureMorphism (power L m) hpos hG,
    generatedToImage_structure X.structureMorphism (power L m) hpos hG,
    generatedToImage_isProper X.structureMorphism (power L m) hpos hG,
    generatedToImage_surjective X.structureMorphism (power L m) hpos hG,
    generatedToImage_isBirationalScheme X.structureMorphism (power L m) hpos hG hbir,
    imageLine X.structureMorphism (power L m) hpos,
    imageLine_isAmple X.structureMorphism (power L m) hpos,
    ⟨generatedToImage_pullbackImageLineIso X.structureMorphism (power L m) hpos hG⟩, ?_⟩
  intro C
  exact generatedToImage_factors_iff X L m hm hpos hG C

end KltDP.Geometry.PrimeCurveImageContraction
