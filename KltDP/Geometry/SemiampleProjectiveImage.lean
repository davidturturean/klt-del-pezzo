import KltDP.Geometry.SemiampleProjectiveRealization
import KltDP.Geometry.LinearSystemImageAmple

/-!
# An actual ample projective image of a semiample power

For an integral proper source the constructed power-system morphism
factors properly and surjectively onto its actual integral projective
image. The image carries the actual restriction of degree one, an ample
invertible sheaf whose original pullback is the chosen positive power.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.SemiampleProjectiveMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSheafSectionPowers

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (L : InvertibleSheaf X) (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- Semiampleness constructs the actual integral projective image, a proper
surjection onto it, and an ample sheaf realizing an actual positive power. -/
theorem exists_integral_projective_image (hL : Positivity.IsSemiample L) :
    ∃ m : ℕ, 0 < m ∧ ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (CommRingCat.of k)),
      IsProjectiveOverField σ ∧ IsIntegral Y ∧ ∃ π : X ⟶ Y,
        π ≫ σ = f ∧ IsProper π ∧ Surjective π ∧ ∃ A : InvertibleSheaf Y,
          AmpleSerre.IsAmple A ∧
          Nonempty ((pullbackInvertibleSheaf π A).obj ≅ (power L m).obj) := by
  letI : CompactSpace X := (quasiCompact_over_affine_iff f).mp inferInstance
  let D := powerSystem L isCompact_univ hL
  let M := power L D.exponent
  let g := LinearSystemMorphism.morphism M D.sections f D.covers
  exact ⟨D.exponent, D.positive, SchematicImageGlued.image g,
    LinearSystemMorphism.imageStructure M D.sections f D.covers,
    LinearSystemMorphism.imageStructure_isProjective M D.sections f D.covers,
    LinearSystemMorphism.image_isIntegral M D.sections f D.covers,
    SchematicImageGlued.toImage g,
    LinearSystemMorphism.toImage_structure M D.sections f D.covers,
    LinearSystemMorphism.toImage_isProper M D.sections f D.covers,
    LinearSystemMorphism.toImage_surjective M D.sections f D.covers,
    LinearSystemMorphism.imageLine M D.sections f D.covers,
    LinearSystemMorphism.imageLine_isAmple M D.sections f D.covers,
    ⟨LinearSystemMorphism.toImage_pullbackImageLineIso M D.sections f D.covers⟩⟩

end KltDP.Geometry.SemiampleProjectiveMap
