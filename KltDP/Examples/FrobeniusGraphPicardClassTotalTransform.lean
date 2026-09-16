import KltDP.Examples.FrobeniusGraphPicardClassFiberClasses
import KltDP.Examples.FrobeniusGlobalBlowupStages

/-!
# The original graph class on the actual contact stages

Pull back the original graph and the two literal fiber ideals through the
constructed composite of actual point-blowup projections. Their integral
Picard classes satisfy the original graph relation on every entire stage.
The graph line also agrees with successive one-step sheaf pullback.

These are total transforms of the original invertible sheaves. Identifying
the actual schematic strict-transform ideal with the total graph ideal
after removing exceptional ideal factors remains a separate obligation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassTotalTransform

open KltDP.Geometry
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassFiberClasses
open FrobeniusGlobalBlowupStages

variable {k : Type u} [Field k]

/-- The actual sheaf pullback of the original graph ideal to the entire stage. -/
def graphTotalIdealLine (n p : ℕ) : InvertibleSheaf (projectiveContactStage (k := k) n) :=
  pullbackInvertibleSheaf (projectiveContactProjection n) (graphIdealLine p)

/-- The total fiber class is the inverse of the actual pulled-back x=1 ideal. -/
def firstFiberTotalClass (n : ℕ) : Additive (projectiveContactStage (k := k) n).Pic :=
  -Additive.ofMul
    (pullbackInvertibleSheaf (projectiveContactProjection n)
      (verticalFiberIdealLine (k := k))).toPic

/-- The total fiber class is the inverse of the actual pulled-back y=1 ideal. -/
def secondFiberTotalClass (n : ℕ) : Additive (projectiveContactStage (k := k) n).Pic :=
  -Additive.ofMul (graphTotalIdealLine (k := k) n 0).toPic

/-- The original integral graph relation transported to the actual whole stage. -/
theorem inverse_graphTotalIdeal_picard_eq_actual_fibers (n p : ℕ) :
    -Additive.ofMul (graphTotalIdealLine (k := k) n p).toPic =
      p • firstFiberTotalClass n + secondFiberTotalClass n := by
  let P := schemePicardPullbackHom (projectiveContactProjection (k := k) n)
  have h := congrArg P.toAdditive
    (inverse_graphIdeal_picard_eq_actual_fibers (k := k) p)
  simp only [firstFiberClass, secondFiberClass, map_neg, map_add, map_nsmul] at h
  change -Additive.ofMul (P (graphIdealLine p).toPic) =
    p • (-Additive.ofMul (P (verticalFiberIdealLine (k := k)).toPic)) +
      (-Additive.ofMul (P (graphIdealLine 0).toPic)) at h
  simpa only [P, schemePicardPullbackHom_toPic, graphTotalIdealLine,
    firstFiberTotalClass, secondFiberTotalClass] using h

/-- The line class at the next actual stage is its actual one-step pullback. -/
theorem graphTotalIdealLine_succ (n p : ℕ) :
    schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)
        (graphTotalIdealLine n p).toPic =
      (graphTotalIdealLine (n + 1) p).toPic := by
  unfold graphTotalIdealLine
  rw [← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic]
  have hcomp : projectiveContactProjection (k := k) (n + 1) =
      (projectiveProductInitial (k := k)).stepProjection n ≫
        projectiveContactProjection n := rfl
  rw [hcomp, schemePicardPullbackHom_comp, MonoidHom.comp_apply]

end KltDP.Examples.FrobeniusGraphPicardClassTotalTransform
