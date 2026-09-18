import KltDP.Geometry.GeneratedCompleteSystemImage
import KltDP.Geometry.SemiampleLargePower

/-!
An eventually birational semiample line gives an actual proper surjective
birational morphism to an integral projective scheme. The target is the
original schematic image of a sufficiently large generated complete system.
Its actual ample image line pulls back to the chosen positive power.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SemiampleProjectiveMap

open CompleteLinearSystemMap InvertibleSheafSectionPowers

/-- Choose a large generated complete system and its actual birational projective image. -/
theorem exists_integral_projective_birational_image
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (L : InvertibleSheaf X)
    (hsemi : Positivity.IsSemiample L)
    (hevent : KeelCompleteSystem.EventuallyBirational f L) :
    ∃ m : ℕ, 0 < m ∧ ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (CommRingCat.of k)),
      IsProjectiveOverField σ ∧ ∃ hY : IsIntegral Y,
        letI : IsIntegral Y := hY
        ∃ π : X ⟶ Y, π ≫ σ = f ∧ IsProper π ∧ Surjective π ∧
          IsBirationalScheme π ∧ ∃ A : InvertibleSheaf Y, AmpleSerre.IsAmple A ∧
            Nonempty ((pullbackInvertibleSheaf π A).obj ≅ (power L m).obj) := by
  obtain ⟨N, _, hN⟩ := hevent
  obtain ⟨m, hm, hmN, hG⟩ :=
    SemiampleActualPowers.exists_globallyGenerated_power_ge L hsemi N
  obtain ⟨hpos, hbir⟩ := hN m hmN
  refine ⟨m, hm, SchematicImageGlued.image (morphism f (power L m) hpos),
    imageStructure f (power L m) hpos, imageStructure_isProjective f (power L m) hpos,
    image_isIntegral f (power L m) hpos, generatedToImage f (power L m) hpos hG,
    generatedToImage_structure f (power L m) hpos hG,
    generatedToImage_isProper f (power L m) hpos hG,
    generatedToImage_surjective f (power L m) hpos hG,
    generatedToImage_isBirationalScheme f (power L m) hpos hG hbir,
    imageLine f (power L m) hpos, imageLine_isAmple f (power L m) hpos,
    ⟨generatedToImage_pullbackImageLineIso f (power L m) hpos hG⟩⟩

end KltDP.Geometry.SemiampleProjectiveMap
