import KltDP.Examples.FrobeniusTowerPicardGeneration
import KltDP.Examples.ProjectiveLineProductPicardGeneration

/-!
# The original rulings and exceptional classes generate each single-centre stage

The proved generation of the original product Picard group by its original
two ruling classes is composed with the actual finite-tower decomposition.
Every Picard class is an integral combination of the two actual ruling
pullbacks and the `n` actual total exceptional classes. No source Picard
generation statement is a premise. Numerical-quotient and multi-centre
coordinate comparisons remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u

namespace KltDP.Examples.FrobeniusTowerRulingGeneration

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusTowerPicardSplitting
open FrobeniusProjectivePoints FrobeniusGraphPicardClassFiberClasses

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Pullback of the original first ruling class along the original tower projection. -/
def firstRulingPullback (n : ℕ) : (projectiveContactStage (k := k) n).Pic :=
  schemePicardPullbackHom ((projectiveProductInitial (k := k)).toInitial n)
    (firstFiberClass (k := k)).toMul

/-- Pullback of the original second ruling class along the original tower projection. -/
def secondRulingPullback (n : ℕ) : (projectiveContactStage (k := k) n).Pic :=
  schemePicardPullbackHom ((projectiveProductInitial (k := k)).toInitial n)
    (secondFiberClass (k := k)).toMul

/-- The actual two ruling pullbacks and all actual total exceptional classes generate. -/
theorem generated_by_rulings_and_exceptional (n : ℕ)
    (L : (projectiveContactStage (k := k) n).Pic) :
    ∃ x y : ℤ, ∃ a : Fin n → ℤ,
      L = firstRulingPullback n ^ x * secondRulingPullback n ^ y *
        ∏ i : Fin n, totalExceptionalClass n i ^ a i := by
  obtain ⟨c, a, hc⟩ := generated_by_base_and_exceptional n L
  obtain ⟨x, y, hxy⟩ :=
    ProjectiveLineProductPicardGeneration.picardClass_eq_zsmul_fibers (Additive.ofMul c)
  have hclass : c = (firstFiberClass (k := k)).toMul ^ x *
      (secondFiberClass (k := k)).toMul ^ y := by
    simpa only [_root_.toMul_ofMul, _root_.toMul_add, _root_.toMul_zsmul] using
      congrArg (fun z : Additive (projectiveProduct k).Pic => z.toMul) hxy
  refine ⟨x, y, a, ?_⟩
  rw [hc, hclass, map_mul, map_zpow, map_zpow]
  rfl

end KltDP.Examples.FrobeniusTowerRulingGeneration
