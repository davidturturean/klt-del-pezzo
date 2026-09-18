import KltDP.Geometry.ResolutionContractionInduction
import KltDP.Geometry.PointBlowupSequenceCohomologyLiteralUse
import KltDP.Geometry.SchemeIsoStructureCohomologyDimension

/-!
# Original structure-sheaf cohomology under a regular-target resolution

The existing actual contraction induction reduces the original resolution
to original point blowups and an isomorphism over the original field.
Their compiled cohomology comparisons preserve every native dimension.
No factorization or cohomological conclusion is a supplied hypothesis.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open ModuleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

/-- Every original O-cohomology dimension survives an actual resolution
whose original target is regular. -/
theorem IsResolution.structureSheaf_cohomologyDimension_eq_of_regular_target
    (hres : IsResolution S X π)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x) (n : ℕ) :
    cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) n =
      cohomologyDimension X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) n := by
  let P : NormalProjectiveSurface k → Prop := fun T =>
    cohomologyDimension T.structureMorphism
        (_root_.SheafOfModules.unit T.toScheme.ringCatSheaf) n =
      cohomologyDimension X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) n
  apply hres.regular_target_induction hX P
  · intro T g hg hgk
    letI : IsIso g := hg
    exact schemeIsoStructure_cohomologyDimension_eq
      (asIso g) T.structureMorphism X.structureMorphism hgk n
  · intro T T' hT E b hminus hb ih
    exact (NativePointBlowupCohomology.contraction_dimension_eq hb n).trans ih

/-- Equality of every actual dimension preserves the native Euler expression. -/
theorem IsResolution.structureSheaf_eulerCharacteristic_eq_of_regular_target
    (hres : IsResolution S X π)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x) :
    eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) =
      eulerCharacteristic X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) := by
  unfold eulerCharacteristic
  simp only [hres.structureSheaf_cohomologyDimension_eq_of_regular_target hX]

end KltDP.Geometry

#check @KltDP.Geometry.IsResolution.structureSheaf_cohomologyDimension_eq_of_regular_target
#print axioms KltDP.Geometry.IsResolution.structureSheaf_cohomologyDimension_eq_of_regular_target
