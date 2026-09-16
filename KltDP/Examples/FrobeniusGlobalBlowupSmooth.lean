import KltDP.Examples.FrobeniusGlobalBlowupStages

/-!
# Smoothness of the entire explicit contact-blowup stages

The initial product is smooth of relative dimension two over `k`, using
its actual polynomial projective-line charts and smooth base change. For
each constructed point blowup, its actual two-piece gluing cover consists
of the smooth polynomial-plane Rees blowup and an unchanged open subset.
Source locality therefore proves smoothness of the entire next scheme.

These are the explicit stages with their proved plane charts. No assertion
that every smooth point has a polynomial-plane open neighborhood is used.
Global strict-transform closures, their divisor intersections, and the
simultaneous configuration at several distinct fibers remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusGlobalBlowupSmooth

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
open FrobeniusGlobalBlowupStages

variable {k : Type u} [Field k]

/-- The two actual polynomial charts prove smooth relative dimension one
for the original projective-line structure morphism. -/
instance projectiveLine_structure_smoothOne :
    IsSmoothOfRelativeDimension 1 (projectiveSpaceToSpec k 1) := by
  apply IsLocalAtSource.of_openCover (P := @IsSmoothOfRelativeDimension 1)
    (ProjectiveLineComparison.polynomialAffineCover k).openCover
  intro i
  change IsSmoothOfRelativeDimension 1
    (ProjectiveLineComparison.polynomialChartMap k i ≫ projectiveSpaceToSpec k 1)
  rw [ProjectiveLineComparison.polynomialChartMap_structureMap]
  infer_instance

/-- The original projective product is smooth of relative dimension two
by actual base change of the second projective-line structure map. -/
instance projectiveProduct_structure_smoothTwo :
    IsSmoothOfRelativeDimension 2
      (FrobeniusProjectivePoints.projectiveProductToSpec (k := k)) := by
  letI : MorphismProperty.IsStableUnderBaseChange (@IsSmoothOfRelativeDimension 1) :=
    isSmoothOfRelativeDimension_isStableUnderBaseChange 1
  letI : IsSmoothOfRelativeDimension 1
      (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)) :=
    MorphismProperty.pullback_fst (P := @IsSmoothOfRelativeDimension 1)
      (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) inferInstance
  change IsSmoothOfRelativeDimension (1 + 1)
    (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) ≫
      projectiveSpaceToSpec k 1)
  infer_instance

namespace ExplicitStages

variable (A : PlaneChartedScheme k)

/-- The actual gluing cover proves preservation of smooth relative
dimension two for the entire next explicit point-blowup stage. -/
instance nextStructure_smoothTwo [IsSmoothOfRelativeDimension 2 A.structureMap] :
    IsSmoothOfRelativeDimension 2 A.nextStructure := by
  letI : (originPoint (k := k)).asIdeal.IsMaximal :=
    FrobeniusBlowupChartIteration.centerIdeal_isMaximal
  apply IsLocalAtSource.of_openCover (P := @IsSmoothOfRelativeDimension 2)
    (KltDP.SchemeTwoOpenGluing.data
      (PointBlowupGluing.overlapOpen (originPoint (k := k))).ι
      (PointBlowupGluing.overlapToPuncture A.chart (originPoint (k := k))
        A.center_closed)).openCover
  intro i
  cases i with
  | left =>
      change IsSmoothOfRelativeDimension 2 (A.nextAffineBlowup ≫ A.nextStructure)
      rw [PlaneChartedScheme.nextStructure, ← Category.assoc,
        PlaneChartedScheme.nextAffineBlowup_projection, Category.assoc, A.chart_structure]
      exact blowupStructure_smoothTwo
  | right =>
      change IsSmoothOfRelativeDimension 2
        (PointBlowupGluing.complementι A.chart (originPoint (k := k)) A.center_closed ≫
          (PointBlowupGluing.projection A.chart (originPoint (k := k)) A.center_closed ≫
            A.structureMap))
      rw [← Category.assoc, PointBlowupGluing.complementι_projection]
      exact inferInstanceAs (IsSmoothOfRelativeDimension (0 + 2)
        ((PointBlowupGluing.puncture A.chart (originPoint (k := k)) A.center_closed).ι ≫
          A.structureMap))

/-- Every finite actual stage remains smooth of relative dimension two. -/
instance stageStructure_smoothTwo [IsSmoothOfRelativeDimension 2 A.structureMap] (n : ℕ) :
    IsSmoothOfRelativeDimension 2 (A.stage n).structureMap := by
  induction n with
  | zero => exact inferInstanceAs (IsSmoothOfRelativeDimension 2 A.structureMap)
  | succ n ih =>
      letI : IsSmoothOfRelativeDimension 2 (A.stage n).structureMap := ih
      change IsSmoothOfRelativeDimension 2 (A.stage n).nextStructure
      infer_instance

end ExplicitStages

instance projectiveProductInitial_structure_smoothTwo :
    IsSmoothOfRelativeDimension 2 (projectiveProductInitial (k := k)).structureMap :=
  projectiveProduct_structure_smoothTwo

/-- Each entire contact stage over the actual projective product is smooth
of relative dimension two over the original coefficient field. -/
instance projectiveContactStage_structure_smoothTwo (n : ℕ) :
    IsSmoothOfRelativeDimension 2 ((projectiveProductInitial (k := k)).stage n).structureMap :=
  ExplicitStages.stageStructure_smoothTwo projectiveProductInitial n

/-- The same actual structure morphism is smooth in the ungraded sense. -/
instance projectiveContactStage_structure_smooth (n : ℕ) :
    IsSmooth ((projectiveProductInitial (k := k)).stage n).structureMap :=
  IsSmoothOfRelativeDimension.isSmooth 2 _

end KltDP.Examples.FrobeniusGlobalBlowupSmooth
