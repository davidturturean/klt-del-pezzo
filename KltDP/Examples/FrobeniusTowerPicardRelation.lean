import KltDP.Examples.FrobeniusFiberPicard

/-!
# The Picard relation of the whole contact tower: `π^*F = F̃ + Σ_j (j+1)·C_j + N·P`

Lane A2 (modules copied byte-identically into this tree together with their import closure) gives, on
the stage `N` of the origin contact tower and in `Additive Pic`, the class of the strict fibre
`F̃_N = F_0^{(N)} − Σ_{j<N} E_j` (`fiberPicardClass_tower`, under the stage-`0` invertibility hypothesis
`FiberKernelInvertible 0`), the classes of the older exceptional curves `C_j = E_j − E_{j+1}`
(`oldExceptionalStrictClasses_tower`) and the newest exceptional class `P = E_{N-1}`
(`totalExceptionalClass_last`). A telescoping identity in any additive commutative group
(`telescope_castSucc`) turns these into the manuscript's relation

  `F_0^{(N+1)} = F̃_{N+1} + Σ_{j<N} (j+1) • C_j + (N+1) • P`   (`fiberTotal_eq_strict_add_exceptional`),

i.e. `b = [F̃] + Σ j [C_j] + p [P]` on the `p`-fold tower once `F_0^{(N)}` is identified with `b`
(that identification and the stage-`0` hypothesis are not proved in lane A2 nor here). Bundle
`f29_tower_fiber_picard_relation` with universe check.
-/

noncomputable section

open CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusTowerPicardRelation

/-! ## A telescoping identity -/

/-- `Σ_{j<N} (j+1)(E_j − E_{j+1}) + (N+1) E_N = Σ_{j≤N} E_j` in an additive commutative group. -/
theorem telescope_castSucc {G : Type*} [AddCommGroup G] :
    ∀ (N : ℕ) (E : Fin (N + 1) → G),
      ∑ j : Fin N, (j.val + 1) • (E j.castSucc - E j.succ) + (N + 1) • E (Fin.last N) =
        ∑ j : Fin (N + 1), E j := by
  intro N
  induction N with
  | zero =>
    intro E
    rw [Fin.sum_univ_zero, Fin.sum_univ_one, zero_add, zero_add, one_smul]
    rfl
  | succ N ih =>
    intro E
    have h := ih (fun j => E j.castSucc)
    rw [Fin.sum_univ_castSucc (f := fun j : Fin (N + 1) => (j.val + 1) • (E j.castSucc - E j.succ)),
      Fin.sum_univ_castSucc (f := E)]
    simp only [Fin.coe_castSucc, Fin.succ_castSucc, Fin.val_last, Fin.succ_last,
      Nat.succ_eq_add_one] at h ⊢
    rw [← h, nsmul_sub, succ_nsmul (E (Fin.last (N + 1))) (N + 1)]
    abel

end KltDP.Examples.FrobeniusTowerPicardRelation

namespace KltDP.Examples.FrobeniusTowerPicardRelation

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStrictTransformClassesTower
  FrobeniusOldExceptionalLaterStages FrobeniusFiberPicard

variable {k : Type u} [Field k]

/-- The older exceptional class as the difference of consecutive total exceptional classes, indexed by
`Fin`. -/
theorem oldExceptionalStrictClass_eq_castSucc (N : ℕ) (j : Fin N) :
    oldExceptionalStrictClass (k := k) (N + 1) j.val (by omega) =
      totalExceptionalClass (N + 1) (Fin.castSucc j) - totalExceptionalClass (N + 1) j.succ :=
  oldExceptionalStrictClasses_tower (N + 1) j.val (by omega)

/-- **The tower relation**: the total transform of the stage-`0` fibre is the strict fibre plus the
weighted older exceptional curves plus `(N+1)` times the newest exceptional class, on stage `N+1`. -/
theorem fiberTotal_eq_strict_add_exceptional (h0 : FiberKernelInvertible (k := k) 0) (N : ℕ) :
    fiberTotalClass h0 (N + 1) =
      fiberPicardClass h0 (N + 1) +
        ∑ j : Fin N, (j.val + 1) • oldExceptionalStrictClass (k := k) (N + 1) j.val (by omega) +
          (N + 1) • totalExceptionalClass (N + 1) (Fin.last N) := by
  have h := fiberPicardClass_tower h0 (N + 1)
  rw [eq_sub_iff_add_eq] at h
  rw [← h, add_assoc]
  congr 1
  simp_rw [oldExceptionalStrictClass_eq_castSucc]
  exact (telescope_castSucc N (totalExceptionalClass (N + 1))).symm

end KltDP.Examples.FrobeniusTowerPicardRelation

namespace KltDP.Examples

open FrobeniusStrictTransformClassesTower FrobeniusOldExceptionalLaterStages FrobeniusFiberPicard
  FrobeniusTowerPicardRelation

/-- Bundle: on every stage `N + 1` of the origin contact tower, under the stage-`0` invertibility
hypothesis, `π^*F_0 = F̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P` in `Additive Pic`. -/
theorem f29_tower_fiber_picard_relation (k : Type u) [Field k]
    (h0 : FiberKernelInvertible (k := k) 0) :
    ∀ N : ℕ, fiberTotalClass h0 (N + 1) =
      fiberPicardClass h0 (N + 1) +
        ∑ j : Fin N, (j.val + 1) • oldExceptionalStrictClass (k := k) (N + 1) j.val (by omega) +
          (N + 1) • totalExceptionalClass (N + 1) (Fin.last N) :=
  fun N => fiberTotal_eq_strict_add_exceptional h0 N

/-- The bundle has exactly one universe parameter. -/
theorem f29_tower_fiber_picard_relation_universe_check (k : Type u) [Field k]
    (h0 : FiberKernelInvertible (k := k) 0) : True := by
  have _ := f29_tower_fiber_picard_relation.{u} k h0
  trivial

end KltDP.Examples
