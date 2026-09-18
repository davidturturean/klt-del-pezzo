import KltDP.Geometry.BirationalOverStructureCohomology
import KltDP.Geometry.ProjectiveLineProductStructureCohomologyConditional
import KltDP.Examples.ProjectiveLineProductRationality

/-!
# Structure cohomology of an original rational regular projective surface

The actual rationality witness gives an original birational correspondence
with P1 times P1. Its actual common resolution transports native cohomology
from the computed product model. The complete ruled-surface source remains
an explicit parameter until the reviewed literal is selected. Rationality
of the original surface is a geometric input, not a claim about every klt model.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open KltDP.Examples.FrobeniusStageZeroProjective
open KltDP.Examples.FrobeniusRulingClassPairing

variable (hGenus :
∀ (k : Type u) [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
  [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
  (hCdim : topologicalKrullDim C = 1)
  (hCreg : ∀ y : C, RegularPoint C y)
  (π : X.toScheme ⟶ C)
  (hbase : π ≫ c = X.structureMorphism)
  (hsurj : Function.Surjective π.base)
  (hfib : ∀ y : C, IsClosed ({y} : Set C) →
    ∃ e : π.fiber y ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 =
        π.fiberι y ≫ X.structureMorphism)
  (σ : C ⟶ X.toScheme) (hσ : σ ≫ π = 𝟙 C),
  (eulerCharacteristic X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) - 1 =
    -(CurveCanonical.genus c : ℤ)) ∧
  (cohomologyDimension X.structureMorphism
      (relativeDifferentialExterior X.structureMorphism 2) 0 = 0) ∧
  (cohomologyDimension X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 1 =
    CurveCanonical.genus c)
)

variable {k : Type u} [Field k] [IsAlgClosed k]

include hGenus in
/-- Actual rationality and original regularity give chi(O)=1 and h1=h2=0. -/
theorem structureCohomology_of_rational_conditional
    (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hrational : Scheme.BirationalOver S.structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) :
    eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) = 1 ∧
      cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 = 0 ∧
      cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 2 = 0 := by
  let T := projectiveProductSurface (k := k)
  have hST : Scheme.BirationalOver S.structureMorphism T.structureMorphism :=
    hrational.trans
      KltDP.Examples.ProjectiveLineProductRationality.birationalOver_affinePlane.symm
  have hmodel :=
    ProjectiveLineProductStructureCohomologyConditional.values hGenus (k := k)
  have hd (n : ℕ) :=
    structureSheaf_cohomologyDimension_eq_of_birationalOver S T hS baseRegular hST n
  have he := structureSheaf_eulerCharacteristic_eq_of_birationalOver
    S T hS baseRegular hST
  exact ⟨he.trans hmodel.1, (hd 1).trans hmodel.2.2.1, (hd 2).trans hmodel.2.2.2⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.structureCohomology_of_rational_conditional
#print axioms KltDP.Geometry.NormalProjectiveSurface.structureCohomology_of_rational_conditional
