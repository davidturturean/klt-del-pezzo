import KltDP.Geometry.PrimeCurveProjectiveImageCriterion
import KltDP.Geometry.GeneratedCompleteSystemImage

/-!
# Exact prime curves contracted by the original generated complete-system image

The criterion specializes to the actual image, closed projective inclusion,
image line, and whole-source image factor already constructed. All map and
line comparisons are original producer theorems, not additional witnesses.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.PrimeCurveImageContraction

open CompleteLinearSystemMap CompleteLinearSystemSections InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k) (L : InvertibleSheaf X.toScheme)
  (m : ℕ) (hm : 0 < m)
  (hpos : 0 < dimension X.structureMorphism (power L m))
  (hG : Positivity.IsGloballyGenerated (power L m).obj)

include hm in
/-- For the actual whole-source generated complete-system image factor,
an original prime curve is constant exactly when its original L-degree is zero. -/
theorem generatedToImage_factors_iff (C : X.PrimeCurve) :
    (∃ p : Spec (CommRingCat.of k) ⟶
        SchematicImageGlued.image (morphism X.structureMorphism (power L m) hpos),
      C.inclusion ≫ generatedToImage X.structureMorphism (power L m) hpos hG =
        C.toSpec ≫ p ∧
      p ≫ imageStructure X.structureMorphism (power L m) hpos = 𝟙 _) ↔
      C.restrictionDegree L = 0 :=
  factors_iff_degree_zero_of_imageLine X C L m hm
    (imageStructure X.structureMorphism (power L m) hpos)
    (generatedToImage X.structureMorphism (power L m) hpos hG)
    (generatedToImage_structure X.structureMorphism (power L m) hpos hG)
    (SchematicImageGlued.inclusion (morphism X.structureMorphism (power L m) hpos))
    rfl (imageLine X.structureMorphism (power L m) hpos) (Iso.refl _)
    (generatedToImage_pullbackImageLineIso X.structureMorphism (power L m) hpos hG)

end KltDP.Geometry.PrimeCurveImageContraction
