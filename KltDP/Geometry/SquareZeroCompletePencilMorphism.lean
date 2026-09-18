import KltDP.Geometry.SquareZeroCompleteSectionDimension
import KltDP.Geometry.SquareZeroGlobalGeneration
import KltDP.Geometry.CompleteLinearSystemGlobalMorphism

/-! The proved complete original square-zero pencil gives an actual
morphism to the original projective line, with original O(1) pulling back
to O(F). Connectedness and generic-fiber geometry are separate results. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

local instance completePencilIntegral : IsIntegral X.toScheme := X.integral

include eK in
/-- The complete pencil is constructed from the original divisor and
its proved section space, without assuming any pencil or map. -/
theorem exists_completePencilMorphism_of_nef_squareZero
    (hrational : Scheme.BirationalOver X.structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
    (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2) :
    ∃ g : X.toScheme ⟶ projectiveSpace k 1,
      g ≫ projectiveSpaceToSpec k 1 = X.structureMorphism ∧
      Nonempty ((pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
          cartierDivisorModule X.toScheme F) := by
  let L := cartierDivisorInvertibleSheaf X.toScheme F
  have htwo : CompleteLinearSystemSections.dimension X.structureMorphism L = 2 :=
    (X.squareZero_hZero_eq_two_and_hOne_eq_zero hX K eK hrational F hF hFF hKF).1
  have hpos : 0 < CompleteLinearSystemSections.dimension X.structureMorphism L := by omega
  have hL := X.globallyGenerated_of_nef_squareZero hX K eK hrational F hF hFF hKF
  have hn : CompleteLinearSystemSections.dimension X.structureMorphism L - 1 = 1 := by omega
  have hg : ∃ g : X.toScheme ⟶
      projectiveSpace k (CompleteLinearSystemSections.dimension X.structureMorphism L - 1),
      g ≫ projectiveSpaceToSpec k
        (CompleteLinearSystemSections.dimension X.structureMorphism L - 1) = X.structureMorphism ∧
      Nonempty ((pullbackInvertibleSheaf g (ProjectiveSpaceDegreeOneSheaf.degreeOne k
        (CompleteLinearSystemSections.dimension X.structureMorphism L - 1))).obj ≅ L.obj) :=
    ⟨CompleteLinearSystemGlobalMorphism.morphism X.structureMorphism L hpos hL,
      CompleteLinearSystemGlobalMorphism.morphism_structure X.structureMorphism L hpos hL,
      ⟨CompleteLinearSystemGlobalMorphism.pullbackDegreeOneIso X.structureMorphism L hpos hL⟩⟩
  exact (congrArg (fun n : ℕ => ∃ g : X.toScheme ⟶ projectiveSpace k n,
    g ≫ projectiveSpaceToSpec k n = X.structureMorphism ∧
    Nonempty ((pullbackInvertibleSheaf g
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k n)).obj ≅ L.obj)) hn).mp hg

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.exists_completePencilMorphism_of_nef_squareZero
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_completePencilMorphism_of_nef_squareZero
