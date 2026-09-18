import KltDP.Examples.FrobeniusTowerPicardSplitting
import KltDP.Examples.FrobeniusExceptionalFinalConfiguration
import Mathlib.Algebra.BigOperators.Fin

/-!
# Generation by the original base and total exceptional classes

Every Picard class on the original single-centre stage is uniquely a product
of a class pulled back from the original initial surface and integral powers
of the original exceptional classes pulled back from their creation stages.
The pullbacks use the accepted actual `between` morphisms, not newly chosen
isomorphisms or hypothetical coordinates. No generation assumption on the
initial Picard group is made.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u

namespace KltDP.Examples.FrobeniusTowerPicardSplitting

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStagePicardSplitting
open FrobeniusExceptionalFinalConfiguration

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The actual exceptional class at its creation stage, pulled back along the original tower. -/
def totalExceptionalClass (n : ℕ) (i : Fin n) : (projectiveContactStage (k := k) n).Pic :=
  schemePicardPullbackHom
    (between (projectiveProductInitial (k := k)) (Nat.succ_le_of_lt i.isLt))
    (exceptionalClass (k := k) i.val)

theorem totalExceptionalClass_last (n : ℕ) :
    totalExceptionalClass (k := k) (n + 1) (Fin.last n) = exceptionalClass n := by
  change schemePicardPullbackHom
    (between (projectiveProductInitial (k := k)) (show n + 1 ≤ n + 1 from le_rfl))
      (exceptionalClass (k := k) n) = _
  rw [between_refl, schemePicardPullbackHom_id]
  rfl

theorem totalExceptionalClass_castSucc (n : ℕ) (i : Fin n) :
    totalExceptionalClass (k := k) (n + 1) i.castSucc =
      schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)
        (totalExceptionalClass n i) := by
  change schemePicardPullbackHom
      (between (projectiveProductInitial (k := k))
        (show i.val + 1 ≤ n + 1 from (Nat.succ_le_of_lt i.isLt).trans (Nat.le_succ n)))
        (exceptionalClass (k := k) i.val) = _
  rw [between_succ (projectiveProductInitial (k := k)) (Nat.succ_le_of_lt i.isLt),
    schemePicardPullbackHom_comp, MonoidHom.comp_apply]
  rfl

/-- The finite-tower inverse is expressed in the actual original base and exceptional classes. -/
theorem towerPicardEquiv_symm_apply (n : ℕ)
    (c : (projectiveContactStage (k := k) 0).Pic) (v : Fin n → Multiplicative ℤ) :
    (towerPicardEquiv (k := k) n).symm (c, v) =
      schemePicardPullbackHom ((projectiveProductInitial (k := k)).toInitial n) c *
        ∏ i : Fin n, totalExceptionalClass n i ^ (v i).toAdd := by
  induction n with
  | zero =>
      change c = schemePicardPullbackHom
        ((projectiveProductInitial (k := k)).toInitial 0) c * _
      rw [PlaneChartedScheme.toInitial_zero, schemePicardPullbackHom_id]
      simp
      rfl
  | succ n ih =>
      rw [towerPicardEquiv_succ_symm_apply, ih, map_mul, map_prod,
        Fin.prod_univ_castSucc, PlaneChartedScheme.toInitial_succ,
        schemePicardPullbackHom_comp, MonoidHom.comp_apply]
      simp only [map_zpow, totalExceptionalClass_castSucc, totalExceptionalClass_last]
      exact mul_assoc _ _ _

/-- Actual base pullback and total exceptional classes generate the entire stage Picard group. -/
theorem generated_by_base_and_exceptional (n : ℕ)
    (L : (projectiveContactStage (k := k) n).Pic) :
    ∃ c : (projectiveContactStage (k := k) 0).Pic, ∃ a : Fin n → ℤ,
      L = schemePicardPullbackHom ((projectiveProductInitial (k := k)).toInitial n) c *
        ∏ i : Fin n, totalExceptionalClass n i ^ a i := by
  refine ⟨(towerPicardEquiv n L).1, fun i => ((towerPicardEquiv n L).2 i).toAdd, ?_⟩
  calc
    L = (towerPicardEquiv n).symm (towerPicardEquiv n L) :=
      ((towerPicardEquiv n).symm_apply_apply L).symm
    _ = _ := towerPicardEquiv_symm_apply n _ _

/-- Both the actual initial class and all total exceptional coefficients are unique. -/
theorem unique_tower_decomposition (n : ℕ)
    (L : (projectiveContactStage (k := k) n).Pic) :
    ∃! p : (projectiveContactStage (k := k) 0).Pic × (Fin n → Multiplicative ℤ),
      schemePicardPullbackHom ((projectiveProductInitial (k := k)).toInitial n) p.1 *
        ∏ i : Fin n, totalExceptionalClass n i ^ (p.2 i).toAdd = L := by
  refine ⟨towerPicardEquiv n L, ?_, ?_⟩
  · exact (towerPicardEquiv_symm_apply n _ _).symm.trans
      ((towerPicardEquiv n).symm_apply_apply L)
  · intro p hp
    apply (towerPicardEquiv (k := k) n).symm.injective
    exact (towerPicardEquiv_symm_apply n p.1 p.2).trans
      (hp.trans ((towerPicardEquiv n).symm_apply_apply L).symm)

end KltDP.Examples.FrobeniusTowerPicardSplitting
