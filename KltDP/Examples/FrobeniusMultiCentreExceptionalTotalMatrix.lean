import KltDP.Examples.FrobeniusMultiCentreExceptionalChainNumerics

/-!
# The original total exceptional classes have negative identity intersection matrix

The proved matrix of the original embedded chain components is transported
through the original Picard identities `C_j = E_j - E_(j+1)` and `P = E_last`.
Two finite reverse inductions give the matrix of the actual total-transform
classes, with no numerical input assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreExceptionalTotalMatrix

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreExceptionalGlobalClasses
  FrobeniusMultiCentreGraphExceptionalPairing
  FrobeniusMultiCentreGraphFiberNumericalValues
  FrobeniusMultiCentreExceptionalChainNumerics

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  [Fact (q + 1).Prime] [CharP k (q + 1)]
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

private theorem chainKernelClass_eq_sub (i : Fin n) (r : Fin q) :
    chainKernelClass q n a ha i r.castSucc =
      exceptionalClass (q + 1) n a i r.castSucc -
        exceptionalClass (q + 1) n a i r.succ := by
  rw [chainKernelClass_castSucc]
  exact chainClass_SPn q n a ha i r

/-- The complete tridiagonal matrix of the actual components in one exceptional chain. -/
theorem chainKernel_pairing (i : Fin n) (j l : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj
      (chainKernelClass q n a ha i j) (chainKernelClass q n a ha i l) =
      if j.val = l.val then (if j.val = q then -1 else -2)
      else if j.val + 1 = l.val ∨ l.val + 1 = j.val then 1 else 0 := by
  classical
  by_cases hjl : j.val = l.val
  · have h : j = l := Fin.ext hjl
    subst l
    rw [if_pos rfl]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨r, rfl⟩ | rfl
    · rw [if_neg (show r.castSucc.val ≠ q from ne_of_lt r.isLt)]
      exact chainKernel_pairing_old_self q n a ha hproj i r
    · rw [Fin.val_last, if_pos rfl]
      exact chainKernel_pairing_newest_self q n a ha hproj i
  · rw [if_neg hjl]
    by_cases hadj : j.val + 1 = l.val ∨ l.val + 1 = j.val
    · rw [if_pos hadj]
      rcases hadj with h | h
      · let r : Fin q := ⟨j.val, by have := l.isLt; omega⟩
        have hrc : r.castSucc = j := Fin.ext rfl
        have hrs : r.succ = l := Fin.ext h
        rw [← hrc, ← hrs]
        exact chainKernel_pairing_adjacent q n a ha hproj i r
      · let r : Fin q := ⟨l.val, by have := j.isLt; omega⟩
        have hrc : r.castSucc = l := Fin.ext rfl
        have hrs : r.succ = j := Fin.ext h
        rw [multiPairing_symm, ← hrc, ← hrs]
        exact chainKernel_pairing_adjacent q n a ha hproj i r
    · rw [if_neg hadj]
      apply chainKernel_pairing_nonadjacent q n a ha hproj i j l
      omega

/-- The complete matrix of all original embedded exceptional components. -/
theorem chainKernel_pairing_all (i i' : Fin n) (j l : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj
      (chainKernelClass q n a ha i j) (chainKernelClass q n a ha i' l) =
      if i = i' then
        if j.val = l.val then (if j.val = q then -1 else -2)
        else if j.val + 1 = l.val ∨ l.val + 1 = j.val then 1 else 0
      else 0 := by
  classical
  by_cases hi : i = i'
  · subst i'
    rw [if_pos rfl]
    exact chainKernel_pairing q n a ha hproj i j l
  · rw [if_neg hi]
    exact chainKernel_pairing_foreign q n a ha hproj i i' hi j l

set_option maxHeartbeats 800000 in
/-- Pairing the original total classes with an actual component gives the discrete difference row. -/
theorem totalClass_chainKernel_pairing_same (i : Fin n) (j l : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj
      (exceptionalClass (q + 1) n a i l) (chainKernelClass q n a ha i j) =
      if j.val = l.val then -1 else if j.val + 1 = l.val then 1 else 0 := by
  classical
  let f := multiPairingHom q n a ha hproj (chainKernelClass q n a ha i j)
  change f (exceptionalClass (q + 1) n a i l) = _
  refine Fin.reverseInduction ?_ (fun r hr => ?_) l
  · have h := chainKernel_pairing q n a ha hproj i (Fin.last q) j
    rw [chainKernelClass_last, newestClass_SPn] at h
    change f (exceptionalClass (q + 1) n a i (Fin.last q)) = _ at h
    simp only [Fin.val_last] at h ⊢
    have hj := j.isLt
    split_ifs at h ⊢ <;> omega
  · have hC : f (chainKernelClass q n a ha i r.castSucc) =
        f (exceptionalClass (q + 1) n a i r.castSucc) -
          f (exceptionalClass (q + 1) n a i r.succ) := by
      rw [chainKernelClass_eq_sub, map_sub]
    have hp : f (chainKernelClass q n a ha i r.castSucc) =
        if r.val = j.val then (if r.val = q then -1 else -2)
        else if r.val + 1 = j.val ∨ j.val + 1 = r.val then 1 else 0 :=
      chainKernel_pairing q n a ha hproj i r.castSucc j
    rw [hp, hr] at hC
    simp only [Fin.coe_castSucc, Fin.val_succ] at hC ⊢
    have hj := j.isLt
    have hrlt := r.isLt
    split_ifs at hC ⊢ <;> omega

/-- Original total classes in a foreign cluster have zero degree on every original component. -/
theorem totalClass_chainKernel_pairing_foreign (i i' : Fin n) (hii' : i ≠ i')
    (j l : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj
      (exceptionalClass (q + 1) n a i l) (chainKernelClass q n a ha i' j) = 0 := by
  let f := multiPairingHom q n a ha hproj (chainKernelClass q n a ha i' j)
  change f (exceptionalClass (q + 1) n a i l) = 0
  refine Fin.reverseInduction ?_ (fun r hr => ?_) l
  · have h : f (chainKernelClass q n a ha i (Fin.last q)) = 0 :=
      chainKernel_pairing_foreign q n a ha hproj i i' hii' (Fin.last q) j
    rwa [chainKernelClass_last, newestClass_SPn] at h
  · have h : f (chainKernelClass q n a ha i r.castSucc) = 0 :=
      chainKernel_pairing_foreign q n a ha hproj i i' hii' r.castSucc j
    rwa [chainKernelClass_eq_sub, map_sub, hr, sub_zero] at h

set_option maxHeartbeats 800000 in
/-- The original total exceptional classes in one cluster have negative identity pairing. -/
theorem totalClass_pairing_same (i : Fin n) (j l : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj
      (exceptionalClass (q + 1) n a i j) (exceptionalClass (q + 1) n a i l) =
      if j = l then -1 else 0 := by
  classical
  let f := multiPairingHom q n a ha hproj (exceptionalClass (q + 1) n a i l)
  change f (exceptionalClass (q + 1) n a i j) = _
  refine Fin.reverseInduction ?_ (fun r hr => ?_) j
  · have h := totalClass_chainKernel_pairing_same q n a ha hproj i (Fin.last q) l
    rw [multiPairing_symm, chainKernelClass_last, newestClass_SPn] at h
    change f (exceptionalClass (q + 1) n a i (Fin.last q)) = _ at h
    simp only [Fin.ext_iff, Fin.val_last] at h ⊢
    have hl := l.isLt
    split_ifs at h ⊢ <;> omega
  · have hC : f (chainKernelClass q n a ha i r.castSucc) =
        f (exceptionalClass (q + 1) n a i r.castSucc) -
          f (exceptionalClass (q + 1) n a i r.succ) := by
      rw [chainKernelClass_eq_sub, map_sub]
    have hp : f (chainKernelClass q n a ha i r.castSucc) =
        if r.val = l.val then -1 else if r.val + 1 = l.val then 1 else 0 := by
      change multiPairing (q + 1) n a ha hproj
        (chainKernelClass q n a ha i r.castSucc) (exceptionalClass (q + 1) n a i l) = _
      rw [multiPairing_symm]
      exact totalClass_chainKernel_pairing_same q n a ha hproj i r.castSucc l
    rw [hp, hr] at hC
    simp only [Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ] at hC ⊢
    split_ifs at hC ⊢ <;> omega

/-- Total exceptional classes in different original clusters have intersection zero. -/
theorem totalClass_pairing_foreign (i i' : Fin n) (hii' : i ≠ i')
    (j l : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj
      (exceptionalClass (q + 1) n a i j) (exceptionalClass (q + 1) n a i' l) = 0 := by
  let f := multiPairingHom q n a ha hproj (exceptionalClass (q + 1) n a i' l)
  have hzero (s : Fin (q + 1)) : f (chainKernelClass q n a ha i s) = 0 := by
    change multiPairing (q + 1) n a ha hproj
      (chainKernelClass q n a ha i s) (exceptionalClass (q + 1) n a i' l) = 0
    rw [multiPairing_symm]
    exact totalClass_chainKernel_pairing_foreign q n a ha hproj i' i (Ne.symm hii') s l
  change f (exceptionalClass (q + 1) n a i j) = 0
  refine Fin.reverseInduction ?_ (fun r hr => ?_) j
  · have h := hzero (Fin.last q)
    rwa [chainKernelClass_last, newestClass_SPn] at h
  · have h := hzero r.castSucc
    rwa [chainKernelClass_eq_sub, map_sub, hr, sub_zero] at h

/-- The full original total-transform matrix is minus the identity, including all clusters. -/
theorem totalClass_pairing (i i' : Fin n) (j l : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj
      (exceptionalClass (q + 1) n a i j) (exceptionalClass (q + 1) n a i' l) =
      if i = i' ∧ j = l then -1 else 0 := by
  classical
  by_cases hi : i = i'
  · subst i'
    simpa only [true_and, eq_self] using totalClass_pairing_same q n a ha hproj i j l
  · rw [if_neg (fun h => hi h.1)]
    exact totalClass_pairing_foreign q n a ha hproj i i' hi j l

end KltDP.Examples.FrobeniusMultiCentreExceptionalTotalMatrix
