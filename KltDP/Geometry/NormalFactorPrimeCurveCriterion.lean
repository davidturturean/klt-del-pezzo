import KltDP.Geometry.FiniteFactorConstant
import KltDP.Geometry.GeneratedImagePrimeCurveCriterion
import KltDP.Geometry.GeneratedCompleteSystemNormalFactor

/-!
The original normal factor contracts exactly the same prime curves as its
original complete-system image. Reflection uses the actual finite map
between those targets and constancy on its original affine point fiber.
The existing complete-system image criterion then gives the original
line-degree criterion without a target-projectivity premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.PrimeCurveImageContraction

variable {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (C : X.PrimeCurve)

/-- An original prime curve is a field point before a finite target map
if and only if it is a field point after that map. -/
theorem factors_iff_comp_finite {Z Y : Scheme.{u}}
    (g : X.toScheme ⟶ Z) (π : Z ⟶ Y) [IsFinite π]
    (σ : Y ⟶ Spec (CommRingCat.of k)) :
    (∃ z : Spec (CommRingCat.of k) ⟶ Z,
      C.inclusion ≫ g = C.toSpec ≫ z ∧ z ≫ (π ≫ σ) = 𝟙 _) ↔
    (∃ y : Spec (CommRingCat.of k) ⟶ Y,
      C.inclusion ≫ (g ≫ π) = C.toSpec ≫ y ∧ y ≫ σ = 𝟙 _) := by
  letI : IsProper C.toSpec := C.toSpec_isProper
  constructor
  · rintro ⟨z, hz, hzs⟩
    refine ⟨z ≫ π, ?_, ?_⟩
    · rw [← Category.assoc, hz, Category.assoc]
    · simpa only [Category.assoc] using hzs
  · rintro ⟨y, hy, hys⟩
    obtain ⟨z, hz, hgz⟩ := FiniteFactorConstant.exists_point_lift
      C.toSpec π y (C.inclusion ≫ g) (by simpa only [Category.assoc] using hy)
    refine ⟨z, hgz, ?_⟩
    rw [← Category.assoc, hz, hys]

open CompleteLinearSystemMap CompleteLinearSystemSections InvertibleSheafSectionPowers

variable (L : InvertibleSheaf X.toScheme) (m : ℕ) (hm : 0 < m)
    (hpos : 0 < dimension X.structureMorphism (power L m))
    (hG : Positivity.IsGloballyGenerated (power L m).obj)

include hm in
/-- The original normal-factor map contracts exactly the original degree-zero primes. -/
theorem generatedNormal_factors_iff :
    (∃ p : Spec (CommRingCat.of k) ⟶
        GeneratedCompleteSystemNormalFactor.target X.structureMorphism (power L m) hpos hG,
      C.inclusion ≫ GeneratedCompleteSystemNormalFactor.fromSource
          X.structureMorphism (power L m) hpos hG = C.toSpec ≫ p ∧
      p ≫ GeneratedCompleteSystemNormalFactor.structureMorphism
          X.structureMorphism (power L m) hpos hG = 𝟙 _) ↔
      C.restrictionDegree L = 0 := by
  letI : IsFinite (GeneratedCompleteSystemNormalFactor.toImage
      X.structureMorphism (power L m) hpos hG) :=
    GeneratedCompleteSystemNormalFactor.toImage_isFinite
      X.structureMorphism (power L m) hpos hG
  refine (factors_iff_comp_finite X C
    (GeneratedCompleteSystemNormalFactor.fromSource X.structureMorphism (power L m) hpos hG)
    (GeneratedCompleteSystemNormalFactor.toImage X.structureMorphism (power L m) hpos hG)
    (imageStructure X.structureMorphism (power L m) hpos)).trans ?_
  simpa only [GeneratedCompleteSystemNormalFactor.fromSource_toImage] using
    generatedToImage_factors_iff X L m hm hpos hG C

end KltDP.Geometry.PrimeCurveImageContraction
