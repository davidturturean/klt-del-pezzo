import KltDP.Examples.FrobeniusStagePicardSplitting

/-!
# Actual coordinates of the single-centre Picard splitting

The inverse of the constructed splitting is the original step pullback
times an integral power of the actual newest exceptional class. In particular
these classes generate, and the expression is unique. The formulas unfold
the accepted `splitEquiv` and `kernelEquivInt`; no new geometric input is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStagePicardSplitting

open KltDP.Geometry FrobeniusGlobalBlowupStages

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem picardSplitting_apply_fst (n : ℕ)
    (c : (projectiveContactStage (k := k) (n + 1)).Pic) :
    (picardSplitting n c).1 = retraction n c := rfl

/-- The inverse uses the actual step projection and actual prime-curve class. -/
theorem picardSplitting_symm_apply (n : ℕ)
    (p : (projectiveContactStage (k := k) n).Pic × Multiplicative ℤ) :
    (picardSplitting (k := k) n).symm p =
      schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n) p.1 *
        exceptionalClass n ^ p.2.toAdd := rfl

theorem picardSplitting_pullback (n : ℕ)
    (c : (projectiveContactStage (k := k) n).Pic) :
    picardSplitting n
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n) c) =
        (c, 1) := by
  apply (picardSplitting (k := k) n).symm.injective
  rw [MulEquiv.symm_apply_apply, picardSplitting_symm_apply]
  simp

theorem picardSplitting_exceptional (n : ℕ) :
    picardSplitting (k := k) n (exceptionalClass n) = (1, Multiplicative.ofAdd 1) := by
  apply (picardSplitting (k := k) n).symm.injective
  rw [MulEquiv.symm_apply_apply, picardSplitting_symm_apply]
  simp

/-- Every class has an expression using pullback and the actual exceptional class. -/
theorem decomposition (n : ℕ)
    (c : (projectiveContactStage (k := k) (n + 1)).Pic) :
    c = schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)
          (picardSplitting n c).1 * exceptionalClass n ^ (picardSplitting n c).2.toAdd :=
  ((picardSplitting (k := k) n).symm_apply_apply c).symm

/-- The actual base class and exceptional coefficient are uniquely determined. -/
theorem unique_decomposition (n : ℕ)
    (c : (projectiveContactStage (k := k) (n + 1)).Pic) :
    ∃! p : (projectiveContactStage (k := k) n).Pic × Multiplicative ℤ,
      schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n) p.1 *
        exceptionalClass n ^ p.2.toAdd = c := by
  refine ⟨picardSplitting n c, (decomposition n c).symm, ?_⟩
  intro p hp
  apply (picardSplitting (k := k) n).symm.injective
  exact hp.trans ((picardSplitting (k := k) n).symm_apply_apply c).symm

end KltDP.Examples.FrobeniusStagePicardSplitting
