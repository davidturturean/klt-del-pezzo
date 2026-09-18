import KltDP.Geometry.ProjectiveFieldBaseChange
import KltDP.Geometry.SurfaceProjectiveLineGenericFiber

/-! Projectivity of every original residue-field fiber of a projective
surface mapping to a separated base, including its actual generic fiber. -/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)

local instance projectiveLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

theorem residueFiber_isProjective {Y : Scheme.{u}}
    (f : S.toScheme ⟶ Y) (σ : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated σ]
    (htriangle : f ≫ σ = S.structureMorphism) (y : Y) :
    IsProjectiveOverField (f.fiberToSpecResidueField y) := by
  exact ProjectiveFieldBaseChange.projective_fieldFiber (l := Y.residueField y)
    f σ (by simpa only [htriangle] using S.projective) (Y.fromSpecResidueField y)

theorem projectiveLine_genericFiber_isProjective
    (f : S.toScheme ⟶ projectiveSpace k 1)
    (htriangle : f ≫ projectiveSpaceToSpec k 1 = S.structureMorphism) :
    IsProjectiveOverField
      (f.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))) := by
  exact S.residueFiber_isProjective f (projectiveSpaceToSpec k 1) htriangle _

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.residueFiber_isProjective
#print axioms KltDP.Geometry.NormalProjectiveSurface.projectiveLine_genericFiber_isProjective
