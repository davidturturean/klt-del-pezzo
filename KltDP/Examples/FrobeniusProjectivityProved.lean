import KltDP.Literature.Hartshorne.SurfaceProjectivity
import KltDP.Examples.FrobeniusStageProjectiveOfLiteral
import KltDP.Examples.FrobeniusMultiCentreProjectivity

/-!
# Projectivity of the original contact stages and finite-centre surfaces

The exact published nonsingular-complete-surface theorem is applied to the
already constructed original origin stage. Its actual integrality,
properness, regular stalks and dimension have already been proved.
Existing translations and fibre products then give the original finite-
centre surface's projectivity. No projectivity premise remains in either
consumer, and no new surface or hypothetical chart presentation is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Geometry

universe u

namespace KltDP.Examples.FrobeniusProjectivityProved

open KltDP.Examples.FrobeniusGlobalBlowupStages
  KltDP.Examples.FrobeniusStageProjectiveOfLiteral
  KltDP.Examples.FrobeniusStageDimension

/-- Every original origin contact stage is projective over the original
algebraically closed field, at every natural depth. -/
theorem originalStageProjective (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) :
    IsProjectiveOverField ((projectiveProductInitial (k := k)).stage n).structureMap := by
  exact KltDP.Literature.Hartshorne.nonsingular_complete_surface_projective_literal
    k (projectiveContactStage (k := k) n)
    ((projectiveProductInitial (k := k)).stage n).structureMap
    (stage_isIntegral' (k := k) n) inferInstance inferInstance inferInstance inferInstance
    (stage_regularPoint (k := k) n)
    (projectiveContactStage_topologicalKrullDim (k := k) n)

/-- The original finite-centre structure map is projective, without a
projectivity, distinctness or characteristic premise. -/
theorem originalMultiStructureProjective (k : Type u) [Field k] [IsAlgClosed k]
    (p n : ℕ) (a : Fin n → k) :
    IsProjectiveOverField
      (KltDP.Examples.FrobeniusMultiCentreSurface.multiStructure p n a) :=
  KltDP.Examples.FrobeniusMultiCentreProjectivity.multiStructure_projective_of_origin
    p (originalStageProjective k p) n a

end KltDP.Examples.FrobeniusProjectivityProved

set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.explicit false
set_option pp.maxSteps 1000000
set_option pp.notation false

#check @KltDP.Literature.Hartshorne.nonsingular_complete_surface_projective_literal
#print axioms KltDP.Literature.Hartshorne.nonsingular_complete_surface_projective_literal
#check @KltDP.Examples.FrobeniusProjectivityProved.originalStageProjective
#print axioms KltDP.Examples.FrobeniusProjectivityProved.originalStageProjective
#check @KltDP.Examples.FrobeniusProjectivityProved.originalMultiStructureProjective
#print axioms KltDP.Examples.FrobeniusProjectivityProved.originalMultiStructureProjective
