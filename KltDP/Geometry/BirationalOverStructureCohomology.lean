import KltDP.Geometry.RegularResolutionStructureCohomology
import KltDP.Geometry.CommonResolutionFromBirationalOver

/-!
# Native structure-sheaf cohomology under the original birational correspondence

The actual dense-open isomorphism constructs a common resolution. The
compiled regular-target comparison is applied to its two original maps,
so the result concerns the original structure sheaves and field actions.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open ModuleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Actual birational correspondence preserves every O-cohomology
dimension of the two original regular projective surfaces. -/
theorem structureSheaf_cohomologyDimension_eq_of_birationalOver
    (S T : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
    (h : Scheme.BirationalOver S.structureMorphism T.structureMorphism) (n : ℕ) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) n =
      cohomologyDimension T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) n := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hS
  letI : IsSmooth S.structureMorphism :=
    IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism
  obtain ⟨Z, b, q, hb, hq, _, _⟩ := exists_common_resolution_of_birationalOver S T h
  exact (hb.structureSheaf_cohomologyDimension_eq_of_regular_target hS n).symm.trans
    (hq.structureSheaf_cohomologyDimension_eq_of_regular_target hT n)

/-- The original Euler characteristic is invariant under the same
actual birational correspondence. -/
theorem structureSheaf_eulerCharacteristic_eq_of_birationalOver
    (S T : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
    (h : Scheme.BirationalOver S.structureMorphism T.structureMorphism) :
    eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) =
      eulerCharacteristic T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) := by
  unfold eulerCharacteristic
  simp only [structureSheaf_cohomologyDimension_eq_of_birationalOver S T hS hT h]

end KltDP.Geometry

#check @KltDP.Geometry.structureSheaf_cohomologyDimension_eq_of_birationalOver
#print axioms KltDP.Geometry.structureSheaf_eulerCharacteristic_eq_of_birationalOver
