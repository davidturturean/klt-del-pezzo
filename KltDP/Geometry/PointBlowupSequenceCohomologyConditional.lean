import KltDP.Geometry.PointBlowupCohomologyConditional
import KltDP.Geometry.SchemeIsoStructureCohomologyDimension
import KltDP.Geometry.SurfacePointBlowupSequenceGeometry
import KltDP.Geometry.SmoothSurfaceRegularity

/-!
# Original blowup sequences and contractions preserve structure-sheaf cohomology

The full Hartshorne V.3.4 hypothesis is retained. Every intermediate
surface in a sequence is the original one. Smoothness is derived during
the same induction, so the next point blowup meets the literal source
regularity hypothesis. A contraction supplies its actual point-blowup
presentation and target regularity from its existing definition.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry

open ModuleCohomology

variable (hHartshorne : ∀ (k : Type u) [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (_hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  (P : X.Point) (c : PointBlowupChart X.toScheme P),
  IsIso c.projection.c ∧
    (∀ i : ℕ, 0 < i →
      IsZero
        (((schemeAbelianSheafPushforward c.projection).rightDerived i).obj
          ((_root_.SheafOfModules.toSheaf c.scheme.ringCatSheaf).obj
            (_root_.SheafOfModules.unit c.scheme.ringCatSheaf)))) ∧
    (∀ i : ℕ,
      Nonempty
        (((baseFunctor X.structureMorphism i).obj
            (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf)) ≅
          ((baseFunctor (c.projection ≫ X.structureMorphism) i).obj
            (_root_.SheafOfModules.unit c.scheme.ringCatSheaf)))))

include hHartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T : NormalProjectiveSurface k} {f : S.toScheme ⟶ T.toScheme}

private theorem pointBlowupSequence_smooth_and_dimension
    (h : IsPointBlowupSequence S T f) (n : ℕ) :
    IsSmooth T.structureMorphism → IsSmooth S.structureMorphism ∧
      cohomologyDimension S.structureMorphism
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) n =
        cohomologyDimension T.structureMorphism
          (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) n := by
  induction h with
  | @of_isIso S T f hf hover =>
      intro hT
      letI : IsSmooth T.structureMorphism := hT
      letI := hf
      constructor
      · rw [← hover]
        infer_instance
      · exact schemeIsoStructure_cohomologyDimension_eq
          (asIso f) S.structureMorphism T.structureMorphism hover n
  | @step S S' T b g x hb hg ih =>
      intro hT
      have ih' := ih hT
      letI : IsSmooth S'.structureMorphism := ih'.1
      exact ⟨hb.source_isSmooth,
        (IsPointBlowupAt.structureSheaf_cohomologyDimension_eq hHartshorne hb
          S'.regularPoints_of_isSmooth n).trans ih'.2⟩

/-- Every original cohomology dimension is preserved by a finite sequence
of original point blowups over an actual smooth projective target. -/
theorem IsPointBlowupSequence.structureSheaf_cohomologyDimension_eq
    [IsSmooth T.structureMorphism] (h : IsPointBlowupSequence S T f) (n : ℕ) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) n =
      cohomologyDimension T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) n :=
  (pointBlowupSequence_smooth_and_dimension hHartshorne h n inferInstance).2

/-- The actual structure-sheaf Euler value survives the original sequence. -/
theorem IsPointBlowupSequence.structureSheaf_eulerCharacteristic_eq
    [IsSmooth T.structureMorphism] (h : IsPointBlowupSequence S T f) :
    eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) =
      eulerCharacteristic T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) := by
  unfold eulerCharacteristic
  simp only [IsPointBlowupSequence.structureSheaf_cohomologyDimension_eq hHartshorne h]

/-- Irregularity of the original source and target is equal. -/
theorem IsPointBlowupSequence.irregularity_eq
    [IsSmooth T.structureMorphism] (h : IsPointBlowupSequence S T f) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 =
      cohomologyDimension T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) 1 :=
  IsPointBlowupSequence.structureSheaf_cohomologyDimension_eq hHartshorne h 1

/-- A contraction exposes the original point blowup and literal target
regularity, so no cohomological premise is needed at this use site. -/
theorem IsContraction.structureSheaf_cohomologyDimension_eq
    {E : S.PrimeCurve} (h : IsContraction S T f E) (n : ℕ) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) n =
      cohomologyDimension T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) n := by
  obtain ⟨p, _, _, _, hb⟩ := h.center
  exact IsPointBlowupAt.structureSheaf_cohomologyDimension_eq hHartshorne hb h.regular n

/-- Equality of the original structure-sheaf Euler values for a contraction. -/
theorem IsContraction.structureSheaf_eulerCharacteristic_eq
    {E : S.PrimeCurve} (h : IsContraction S T f E) :
    eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) =
      eulerCharacteristic T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) := by
  obtain ⟨p, _, _, _, hb⟩ := h.center
  exact IsPointBlowupAt.structureSheaf_eulerCharacteristic_eq hHartshorne hb h.regular

/-- The contraction preserves the original degree-one dimension q. -/
theorem IsContraction.irregularity_eq
    {E : S.PrimeCurve} (h : IsContraction S T f E) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 =
      cohomologyDimension T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) 1 :=
  IsContraction.structureSheaf_cohomologyDimension_eq hHartshorne h 1

end KltDP.Geometry

#check @KltDP.Geometry.IsPointBlowupSequence.structureSheaf_eulerCharacteristic_eq
#check @KltDP.Geometry.IsContraction.structureSheaf_eulerCharacteristic_eq
#print axioms KltDP.Geometry.IsPointBlowupSequence.structureSheaf_eulerCharacteristic_eq
#print axioms KltDP.Geometry.IsContraction.irregularity_eq
