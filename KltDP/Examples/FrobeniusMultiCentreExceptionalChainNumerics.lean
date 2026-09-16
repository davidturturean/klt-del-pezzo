import KltDP.Examples.FrobeniusMultiCentreAdjacentIntersection
import KltDP.Examples.FrobeniusMultiCentreGraphFiberNumericalValues
import KltDP.Examples.FrobeniusTowerPicardRelation

/-!
# The actual exceptional chains have the tridiagonal intersection matrix

The original embedded kernel lines, in their original global Picard group,
satisfy the weighted fibre identity. Restricting that identity to an old
exceptional curve gives zero. Actual disjoint supports give the zero entries,
and the proved original adjacent intersections give the two neighbouring
entries. Their weights force every old self-intersection to be minus two.
The newest self-intersection is the already proved minus one.

The numerical statements retain projectivity of the original multi-centre
surface. The old-square argument also retains the characteristic and prime
hypotheses of the accepted strict-fibre class identity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreExceptionalChainNumerics

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
  KltDP.Geometry.PrimeCurveClassPairing
open FrobeniusExceptionalFinalConfiguration FrobeniusExceptionalChainPicard
  FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalPrime
  FrobeniusMultiCentreExceptionalGlobalClasses FrobeniusMultiCentreChainPicard
  FrobeniusMultiCentreGraphExceptionalPairing FrobeniusMultiCentreAdjacentIntersection
  FrobeniusMultiCentreNewestExceptionalSelf FrobeniusMultiCentreExceptionalRulingRows
  FrobeniusMultiCentreFiberGlobalClass FrobeniusMultiCentreFiberExceptionalRows
  FrobeniusMultiCentreGraphFiberNumericalValues

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

/-- The divisor class of an original embedded exceptional chain component. -/
abbrev chainKernelClass (i : Fin n) (j : Fin (q + 1)) :
    Additive (multiSurface (q + 1) n a).Pic :=
  -Additive.ofMul (exceptionalKernelLine q n a ha i (chainMember.{0} q j)).toPic

theorem chainKernelClass_castSucc (i : Fin n) (j : Fin q) :
    chainKernelClass q n a ha i j.castSucc =
      -Additive.ofMul (exceptionalKernelLine q n a ha i (.inl j)).toPic := by
  unfold chainKernelClass
  rw [chainMember_of_lt q j.castSucc j.isLt]
  exact congrArg (fun r : Fin q =>
    -Additive.ofMul (exceptionalKernelLine q n a ha i (.inl r)).toPic) (Fin.ext rfl)

theorem chainKernelClass_last (i : Fin n) :
    chainKernelClass q n a ha i (Fin.last q) =
      -Additive.ofMul (exceptionalKernelLine q n a ha i (.inr PUnit.unit)).toPic := by
  unfold chainKernelClass
  rw [chainMember_of_not_lt q (Fin.last q) (Nat.lt_irrefl q)]

/-- The original weighted chain is the sum of the original total exceptional classes. -/
theorem weighted_chainKernelClass (i : Fin n) :
    ∑ j : Fin (q + 1), (j.val + 1) • chainKernelClass q n a ha i j =
      ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i j := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, chainKernelClass_castSucc,
    chainKernelClass_last, chainClass_SPn, newestClass_SPn]
  exact FrobeniusTowerPicardRelation.telescope_castSucc q (exceptionalClass (q + 1) n a i)

variable (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

private theorem chainKernel_pairing_zero_of_disjoint (i i' : Fin n)
    (j j' : Fin (q + 1))
    (hdisj : Disjoint (exceptionalSupport q n a i (chainMember.{0} q j))
      (exceptionalSupport q n a i' (chainMember.{0} q j'))) :
    multiPairing (q + 1) n a ha hproj
      (chainKernelClass q n a ha i j) (chainKernelClass q n a ha i' j') = 0 := by
  letI := exceptionalCurve_isIntegral q n a ha i (chainMember.{0} q j)
  apply (pairing_kernelLine_left (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i (chainMember.{0} q j) hproj)
    (exceptionalCurveι q n a i (chainMember.{0} q j))
    (coe_exceptionalPrimeCurveSPn q n a ha i (chainMember.{0} q j) hproj)
    (exceptionalKernelLine q n a ha i (chainMember.{0} q j)) rfl _).trans
  apply restrictionDegreeHom_neg_kernel_zero (multiSurfaceSurface (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i (chainMember.{0} q j) hproj)
    (exceptionalCurveι q n a i' (chainMember.{0} q j'))
    (exceptionalKernelLine q n a ha i' (chainMember.{0} q j')) rfl
  rw [PrimeCurve.range_inclusion, coe_exceptionalPrimeCurveSPn]
  exact hdisj

/-- Nonadjacent original components in one chain have intersection zero. -/
theorem chainKernel_pairing_nonadjacent (i : Fin n) (j j' : Fin (q + 1))
    (hjj' : j.val + 1 < j'.val ∨ j'.val + 1 < j.val) :
    multiPairing (q + 1) n a ha hproj
      (chainKernelClass q n a ha i j) (chainKernelClass q n a ha i j') = 0 := by
  apply chainKernel_pairing_zero_of_disjoint q n a ha hproj
  rcases hjj' with h | h
  · exact support_disjoint q n a i j j' h
  · exact (support_disjoint q n a i j' j h).symm

/-- Original exceptional components in different clusters have intersection zero. -/
theorem chainKernel_pairing_foreign (i i' : Fin n) (hii' : i ≠ i')
    (j j' : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj
      (chainKernelClass q n a ha i j) (chainKernelClass q n a ha i' j') = 0 := by
  apply chainKernel_pairing_zero_of_disjoint q n a ha hproj
  exact exceptionalSupport_disjoint_of_ne q n a ha hii' _ _

theorem chainKernel_pairing_adjacent (i : Fin n) (j : Fin q) :
    multiPairing (q + 1) n a ha hproj
      (chainKernelClass q n a ha i j.castSucc) (chainKernelClass q n a ha i j.succ) = 1 :=
  adjacentKernel_pairing_one q n a ha hproj i j

theorem chainKernel_pairing_newest_self (i : Fin n) :
    multiPairing (q + 1) n a ha hproj
      (chainKernelClass q n a ha i (Fin.last q))
      (chainKernelClass q n a ha i (Fin.last q)) = -1 := by
  rw [chainKernelClass_last]
  exact newestKernel_pairing_self q n a ha hproj i

variable [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- The actual fibre plus the original weighted exceptional chain equals the base ruling. -/
theorem secondFiber_eq_fiberKernel_add_weighted_chain (i : Fin n) :
    multiSecondFiberClass (q + 1) n a =
      -Additive.ofMul (fiberKernelLine q n a ha i).toPic +
        ∑ j : Fin (q + 1), (j.val + 1) • chainKernelClass q n a ha i j := by
  rw [weighted_chainKernelClass, fiberClass_SPn]
  abel

/-- The weighted exceptional chain has degree zero on each original old component. -/
theorem weighted_chainKernel_pairing_old_zero (i : Fin n) (j : Fin q) :
    ∑ l : Fin (q + 1), ((l.val + 1 : ℕ) : ℤ) *
      multiPairing (q + 1) n a ha hproj
        (chainKernelClass q n a ha i l) (chainKernelClass q n a ha i j.castSucc) = 0 := by
  let f := multiPairingHom q n a ha hproj (chainKernelClass q n a ha i j.castSucc)
  have h := congrArg f (secondFiber_eq_fiberKernel_add_weighted_chain q n a ha i)
  rw [map_add, map_sum] at h
  simp only [map_nsmul, nsmul_eq_mul] at h
  have hb : f (multiSecondFiberClass (q + 1) n a) = 0 := by
    change multiPairing (q + 1) n a ha hproj (multiSecondFiberClass (q + 1) n a)
      (chainKernelClass q n a ha i j.castSucc) = 0
    rw [multiPairing_symm, chainKernelClass_castSucc]
    exact exceptionalKernel_secondFiber_pairing_zero q n a ha hproj i (.inl j)
  have hf : f (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) = 0 := by
    change multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (fiberKernelLine q n a ha i).toPic)
      (chainKernelClass q n a ha i j.castSucc) = 0
    rw [multiPairing_symm, chainKernelClass_castSucc]
    exact oldKernel_fiberKernel_pairing_eq_zero q n a ha hproj i i j
  rw [hb, hf, zero_add] at h
  exact h.symm

set_option maxHeartbeats 800000 in
/-- Each original older exceptional curve has self-intersection minus two. -/
theorem chainKernel_pairing_old_self (i : Fin n) (j : Fin q) :
    multiPairing (q + 1) n a ha hproj
      (chainKernelClass q n a ha i j.castSucc)
      (chainKernelClass q n a ha i j.castSucc) = -2 := by
  classical
  let S := multiPairing (q + 1) n a ha hproj
    (chainKernelClass q n a ha i j.castSucc) (chainKernelClass q n a ha i j.castSucc)
  have hneq : j.castSucc ≠ j.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.coe_castSucc, Fin.val_succ] at this
    omega
  have hrow (l : Fin (q + 1)) :
      ((l.val + 1 : ℕ) : ℤ) * multiPairing (q + 1) n a ha hproj
        (chainKernelClass q n a ha i l) (chainKernelClass q n a ha i j.castSucc) =
      (if l = j.castSucc then ((j.val + 1 : ℕ) : ℤ) * S else 0) +
        (if l = j.succ then ((j.val + 2 : ℕ) : ℤ) else 0) +
        (if l.val + 1 = j.val then (j.val : ℤ) else 0) := by
    by_cases hl : l = j.castSucc
    · subst l
      simp [hneq, S]
    by_cases hn : l = j.succ
    · subst l
      rw [multiPairing_symm, chainKernel_pairing_adjacent]
      simp [Ne.symm hneq, Nat.add_assoc]
    by_cases hp : l.val + 1 = j.val
    · let r : Fin q := ⟨l.val, by have := j.isLt; omega⟩
      have hrc : r.castSucc = l := Fin.ext rfl
      have hrs : r.succ = j.castSucc := Fin.ext hp
      have hpair : multiPairing (q + 1) n a ha hproj
          (chainKernelClass q n a ha i l) (chainKernelClass q n a ha i j.castSucc) = 1 := by
        rw [← hrc, ← hrs]
        exact chainKernel_pairing_adjacent q n a ha hproj i r
      rw [hpair]
      simp [hl, hn, hp]
    · have hsep : l.val + 1 < j.castSucc.val ∨ j.castSucc.val + 1 < l.val := by
        have hlv : l.val ≠ j.val := fun h => hl (Fin.ext h)
        have hnv : l.val ≠ j.val + 1 := fun h => hn (Fin.ext h)
        simp only [Fin.coe_castSucc]
        omega
      rw [chainKernel_pairing_nonadjacent q n a ha hproj i l j.castSucc hsep]
      simp [hl, hn, hp]
  have hprev : (∑ l : Fin (q + 1), if l.val + 1 = j.val then (j.val : ℤ) else 0) =
      (j.val : ℤ) := by
    by_cases hj : j.val = 0
    · simp [hj]
    · let r : Fin (q + 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
      have heq (l : Fin (q + 1)) : (l.val + 1 = j.val) ↔ l = r := by
        constructor
        · intro h
          apply Fin.ext
          change l.val = j.val - 1
          omega
        · intro h
          subst l
          change j.val - 1 + 1 = j.val
          omega
      simp_rw [heq]
      simp
  have hsum := weighted_chainKernel_pairing_old_zero q n a ha hproj i j
  simp_rw [hrow, Finset.sum_add_distrib] at hsum
  rw [hprev] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  have hjpos : (0 : ℤ) < ((j.val + 1 : ℕ) : ℤ) := by positivity
  have hmul : ((j.val + 1 : ℕ) : ℤ) * (S + 2) = 0 := by
    push_cast at hsum ⊢
    nlinarith [hsum]
  have hz := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hjpos)
  change S = -2
  linarith

end KltDP.Examples.FrobeniusMultiCentreExceptionalChainNumerics
