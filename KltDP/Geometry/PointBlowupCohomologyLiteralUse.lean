import KltDP.Literature.Hartshorne.PointBlowupCohomology
import KltDP.Geometry.PointBlowupCohomologyConditional

/-! Direct original point-blowup consumers of the reviewed full source. -/
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.NativePointBlowupCohomology
open ModuleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
  {p : T.Point}

/-- All original structure-sheaf cohomology is preserved over the original k. -/
theorem linearEquiv_nonempty (hb : IsPointBlowupAt S T b p)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t) (n : ℕ) :
    Nonempty
      (((baseFunctor S.structureMorphism n).obj
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf)) ≃ₗ[k]
        ((baseFunctor T.structureMorphism n).obj
          (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf))) :=
  IsPointBlowupAt.structureSheafHLinearEquiv_nonempty
    Literature.Hartshorne.point_blowup_structure_cohomology_literal hb hT n

/-- Every original cohomology dimension is preserved. -/
theorem dimension_eq (hb : IsPointBlowupAt S T b p)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t) (n : ℕ) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) n =
      cohomologyDimension T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) n :=
  IsPointBlowupAt.structureSheaf_cohomologyDimension_eq
    Literature.Hartshorne.point_blowup_structure_cohomology_literal hb hT n

/-- The actual structure-sheaf Euler value is preserved. -/
theorem euler_eq (hb : IsPointBlowupAt S T b p)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t) :
    eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) =
      eulerCharacteristic T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) :=
  IsPointBlowupAt.structureSheaf_eulerCharacteristic_eq
    Literature.Hartshorne.point_blowup_structure_cohomology_literal hb hT

end KltDP.Geometry.NativePointBlowupCohomology

#check @KltDP.Geometry.NativePointBlowupCohomology.linearEquiv_nonempty
#print axioms KltDP.Geometry.NativePointBlowupCohomology.linearEquiv_nonempty
#print axioms KltDP.Geometry.NativePointBlowupCohomology.dimension_eq
#print axioms KltDP.Geometry.NativePointBlowupCohomology.euler_eq
