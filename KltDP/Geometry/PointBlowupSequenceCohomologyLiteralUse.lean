import KltDP.Geometry.PointBlowupSequenceCohomologyConditional
import KltDP.Literature.Hartshorne.PointBlowupCohomology

/-!
# Native cohomology invariance for original blowup sequences and contractions

The complete reviewed Hartshorne V.3.4 literal discharges the full source
hypothesis of the ordinary consumers. The original schemes, morphisms,
unit sheaves, and base-field cohomology actions remain unchanged.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.NativePointBlowupCohomology

open ModuleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T : NormalProjectiveSurface k} {f : S.toScheme ⟶ T.toScheme}

theorem sequence_dimension_eq [IsSmooth T.structureMorphism]
    (h : IsPointBlowupSequence S T f) (n : ℕ) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) n =
      cohomologyDimension T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) n :=
  IsPointBlowupSequence.structureSheaf_cohomologyDimension_eq
    KltDP.Literature.Hartshorne.point_blowup_structure_cohomology_literal h n

theorem sequence_euler_eq [IsSmooth T.structureMorphism]
    (h : IsPointBlowupSequence S T f) :
    eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) =
      eulerCharacteristic T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) :=
  IsPointBlowupSequence.structureSheaf_eulerCharacteristic_eq
    KltDP.Literature.Hartshorne.point_blowup_structure_cohomology_literal h

theorem sequence_irregularity_eq [IsSmooth T.structureMorphism]
    (h : IsPointBlowupSequence S T f) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 =
      cohomologyDimension T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) 1 :=
  sequence_dimension_eq h 1

theorem contraction_dimension_eq {E : S.PrimeCurve}
    (h : IsContraction S T f E) (n : ℕ) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) n =
      cohomologyDimension T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) n :=
  IsContraction.structureSheaf_cohomologyDimension_eq
    KltDP.Literature.Hartshorne.point_blowup_structure_cohomology_literal h n

theorem contraction_euler_eq {E : S.PrimeCurve}
    (h : IsContraction S T f E) :
    eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) =
      eulerCharacteristic T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) :=
  IsContraction.structureSheaf_eulerCharacteristic_eq
    KltDP.Literature.Hartshorne.point_blowup_structure_cohomology_literal h

theorem contraction_irregularity_eq {E : S.PrimeCurve}
    (h : IsContraction S T f E) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 =
      cohomologyDimension T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) 1 :=
  contraction_dimension_eq h 1

end KltDP.Geometry.NativePointBlowupCohomology

#check @KltDP.Geometry.NativePointBlowupCohomology.sequence_dimension_eq
#print axioms KltDP.Geometry.NativePointBlowupCohomology.sequence_euler_eq
#print axioms KltDP.Geometry.NativePointBlowupCohomology.contraction_irregularity_eq
