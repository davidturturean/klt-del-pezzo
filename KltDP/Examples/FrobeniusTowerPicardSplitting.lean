import KltDP.Examples.FrobeniusStagePicardCoordinates
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The Picard group of the original finite single-centre tower

Iterating the actual one-step splittings gives
`Pic (stage n) ≃* Pic (stage 0) × (Fin n → Multiplicative ℤ)`.
Coordinates are ordered by creation stage, with the newest coefficient last.
The actual composite pullback from the initial surface is the first factor.
The initial Picard group is retained as its original object; no generation
hypothesis or chosen ruling-basis identification is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusTowerPicardSplitting

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStagePicardSplitting

variable {k : Type u} [Field k] [IsAlgClosed k]

private def zeroSplitting :
    (projectiveContactStage (k := k) 0).Pic ≃*
      (projectiveContactStage (k := k) 0).Pic × (Fin 0 → Multiplicative ℤ) where
  toFun c := (c, 1)
  invFun p := p.1
  left_inv _ := rfl
  right_inv _ := Prod.ext rfl (funext fun i => Fin.elim0 i)
  map_mul' _ _ := rfl

/-- The pinned tuple equivalence, preserving the pointwise group operation. -/
private def appendCoordinate (n : ℕ) :
    (Fin n → Multiplicative ℤ) × Multiplicative ℤ ≃*
      (Fin (n + 1) → Multiplicative ℤ) :=
  { (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Multiplicative ℤ)) with
    map_mul' := by
      intro a b
      funext i
      change Fin.snoc (α := fun _ => Multiplicative ℤ) (a.1 * b.1) (a.2 * b.2) i =
        Fin.snoc (α := fun _ => Multiplicative ℤ) a.1 a.2 i *
          Fin.snoc (α := fun _ => Multiplicative ℤ) b.1 b.2 i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc, Pi.mul_apply] }

/-- The original tower's Picard decomposition, retaining its original stage-zero Picard group. -/
def towerPicardEquiv : (n : ℕ) →
    (projectiveContactStage (k := k) n).Pic ≃*
      (projectiveContactStage (k := k) 0).Pic × (Fin n → Multiplicative ℤ)
  | 0 => zeroSplitting
  | n + 1 =>
      (picardSplitting (k := k) n).trans
        ((MulEquiv.prodCongr (towerPicardEquiv n) (MulEquiv.refl (Multiplicative ℤ))).trans
          ((MulEquiv.prodAssoc).trans
            (MulEquiv.prodCongr (MulEquiv.refl _) (appendCoordinate n))))

theorem towerPicardEquiv_zero_apply (c : (projectiveContactStage (k := k) 0).Pic) :
    towerPicardEquiv 0 c = (c, 1) := rfl

theorem towerPicardEquiv_succ_apply (n : ℕ)
    (c : (projectiveContactStage (k := k) (n + 1)).Pic) :
    towerPicardEquiv (n + 1) c =
      ((towerPicardEquiv n (picardSplitting n c).1).1,
        Fin.snoc (towerPicardEquiv n (picardSplitting n c).1).2
          (picardSplitting n c).2) := rfl

/-- The recursive inverse multiplies the actual step pullback by the newest exceptional class. -/
theorem towerPicardEquiv_succ_symm_apply (n : ℕ)
    (c : (projectiveContactStage (k := k) 0).Pic) (v : Fin (n + 1) → Multiplicative ℤ) :
    (towerPicardEquiv (k := k) (n + 1)).symm (c, v) =
      schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)
        ((towerPicardEquiv n).symm (c, fun i => v i.castSucc)) *
          exceptionalClass n ^ (v (Fin.last n)).toAdd := rfl

/-- The original composite pullback is exactly the initial Picard factor. -/
theorem towerPicardEquiv_pullback (n : ℕ)
    (c : (projectiveContactStage (k := k) 0).Pic) :
    towerPicardEquiv n
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).toInitial n) c) =
        (c, 1) := by
  induction n with
  | zero =>
      rw [PlaneChartedScheme.toInitial_zero, schemePicardPullbackHom_id]
      rfl
  | succ n ih =>
      rw [PlaneChartedScheme.toInitial_succ, schemePicardPullbackHom_comp,
        MonoidHom.comp_apply, towerPicardEquiv_succ_apply, picardSplitting_pullback, ih]
      have h : Fin.snoc (1 : Fin n → Multiplicative ℤ) (1 : Multiplicative ℤ) =
          (1 : Fin (n + 1) → Multiplicative ℤ) :=
        (appendCoordinate n).map_one
      exact congrArg (fun v : Fin (n + 1) → Multiplicative ℤ => (c, v)) h

theorem towerPicardSplitting (n : ℕ) :
    Nonempty ((projectiveContactStage (k := k) n).Pic ≃*
      (projectiveContactStage (k := k) 0).Pic × (Fin n → Multiplicative ℤ)) :=
  ⟨towerPicardEquiv (k := k) n⟩

end KltDP.Examples.FrobeniusTowerPicardSplitting
