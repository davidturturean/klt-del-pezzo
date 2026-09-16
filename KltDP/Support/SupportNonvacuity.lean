import KltDP.Support.ReplacementNotation
import KltDP.Support.KltCoefficients
import KltDP.Support.HigherResolutions
import KltDP.Support.NefPositiveSpan
import KltDP.Support.PicardParity
import KltDP.Support.CodeKernelLift
import KltDP.Support.FrobeniusSign
import KltDP.Support.CoreWeights
import KltDP.Support.SectionCount
import KltDP.Support.GraphBridge
import KltDP.Support.AverageDescent
import KltDP.Support.EffectiveSupport
import KltDP.Support.SingleEffectiveArithmetic
import KltDP.Support.EqualityContactCert
import KltDP.Support.WeightedForestCore
import Mathlib.Tactic

/-!
# Nonvacuity witnesses for the Support modules (lane B8)

The plan (§10.3) asks, separately from compilation, that the hypotheses of every
public statement be shown jointly satisfiable by actual witnesses. This module
supplies concrete instances, all checked by `decide`/`norm_num`/explicit terms,
for the hypotheses of the coordinator's Support modules where satisfiability is
not obvious. See `SUPPORT_SEMANTIC_REVIEW.md` for the review and
`SUPPORT_NONVACUITY_CORRESPONDENCE.md` for the witness → module map.

* U-REPLACEMENT-NOTATION: two `ReplacementData ℚ` instances from the equality
  surface `S_{3,3}` at the shortest curve `P_i` (the components meeting `C` or
  `P_i`): with `C = V_i` (the manuscript's excess-contact vertex, Prop. A.2)
  the values are `μ = 0`, `h = η = 2/3`, `α = 0`, `τ = 1`, `ℓ = 1/3`,
  `λ₀ = (1/3, 1/3, 0)` on `(B, F_i, U_i)`; with `C = B` they are `μ = 1/3`,
  `h = 1`, `η = 1/3`, `ℓ = 1/3`. (The brief's "h = η = 2/3, μ = 1/3" mixes the
  two: `μ = 1/3` is the coefficient of a weight-three component, not of `V_i`.)
* U-KLT-COEFFICIENTS: `chainThreeTwo` is positive definite and has the nonzero
  solution `(2/5, 1/5)`; the all-weight-two `A₂` block is positive definite.
* U-HIGHER-RESOLUTIONS: a three-step tower with explicit resulting coefficients.
* U-NEF-POSITIVE-SPAN: `m = 2`.
* U-PICARD-PARITY and U-CODE-KERNEL-LIFT: the unimodular lattice `I_{1,5}`
  with `K = -3h + Σ e_i`, four orthogonal `(-2)`-vectors whose sum is twice
  `h - e₂ - e₃ - e₅`, and the index-`8` sublattice `Γ` of vectors pairing
  evenly with all four nodes (`v₂(8) = 3 < 4`).
* A `WeightedForest` (the leaf-rooted three-leaf star, root weight three),
  an admissible `Contact` (`P 0`), and instances for FrobeniusSign `(3,3)`,
  CoreWeights `(3,4)`, SectionCount `s = 3`, GraphBridge `b = 3`,
  AverageDescent, EffectiveSupport, CountZeroContact (`1 - 2 = -1`),
  SingleEffectiveArithmetic `β = 3`.
* `support_nonvacuity` bundles the witnesses.

No geometric object is constructed; every witness is finite rational/integer
data.
-/

namespace KltDP.Support

open Matrix

namespace SupportNonvacuity

open KltDP.LinearAlgebra KltDP.Manuscript.S09

/-- `![a, b, c, d, e, f] 5 = f`, in the style of the pinned `Matrix.cons_val_four`. -/
theorem cons_val_five {α : Type*} {m : ℕ} (x : α) (u : Fin (m + 5) → α) :
    Matrix.vecCons x u 5 =
      Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))) :=
  rfl

/-! ### U-REPLACEMENT-NOTATION: `S_{3,3}` at `P_i` -/

/-- Block data at `P_i` with `C = V_i`; `D₀ = (B, F_i, U_i)` (the other six
components are orthogonal to `v` and `r` and do not enter the scalars). -/
def replacementAtPi : ReplacementData (Fin 3) ℚ where
  b := 2
  v := ![0, 0, 1]
  M := Matrix.diagonal ![3, 3, 2]
  q0 := ![1, 1, 0]
  m := 1
  r := ![1, 1, 0]

theorem replacementAtPi_M_inv :
    replacementAtPi.M⁻¹ = Matrix.diagonal ![1 / 3, 1 / 3, 1 / 2] := by
  apply Matrix.inv_eq_right_inv
  show Matrix.diagonal ![3, 3, 2] * Matrix.diagonal ![1 / 3, 1 / 3, 1 / 2] = 1
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i => (![3, 3, 2] : Fin 3 → ℚ) i * (![1 / 3, 1 / 3, 1 / 2] : Fin 3 → ℚ) i) =
      fun _ => (1 : ℚ) := by
    funext i
    fin_cases i <;> norm_num
  rw [h, Matrix.diagonal_one]

theorem replacementAtPi_theta : replacementAtPi.theta = ![1 / 3, 1 / 3, 0] := by
  show replacementAtPi.M⁻¹ *ᵥ ![1, 1, 0] = _
  rw [replacementAtPi_M_inv]
  funext i
  fin_cases i <;> norm_num [Matrix.mulVec_diagonal, Matrix.cons_val_two]

theorem replacementAtPi_u : replacementAtPi.u = ![1 / 3, 1 / 3, 0] := by
  show replacementAtPi.M⁻¹ *ᵥ ![1, 1, 0] = _
  rw [replacementAtPi_M_inv]
  funext i
  fin_cases i <;> norm_num [Matrix.mulVec_diagonal, Matrix.cons_val_two]

theorem replacementAtPi_Minv_v : replacementAtPi.M⁻¹ *ᵥ ![0, 0, 1] = ![0, 0, 1 / 2] := by
  rw [replacementAtPi_M_inv]
  funext i
  fin_cases i <;> norm_num [Matrix.mulVec_diagonal, Matrix.cons_val_two]

theorem replacementAtPi_schur : replacementAtPi.schurScalar = 3 / 2 := by
  show (2 : ℚ) - ![0, 0, 1] ⬝ᵥ (replacementAtPi.M⁻¹ *ᵥ ![0, 0, 1]) = 3 / 2
  rw [replacementAtPi_Minv_v]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

/-- The hypotheses of `u_replacement_notation` hold. -/
theorem replacementAtPi_hypotheses :
    IsUnit replacementAtPi.M.det ∧ replacementAtPi.schurScalar ≠ 0 ∧ replacementAtPi.M.IsSymm := by
  refine ⟨?_, ?_, Matrix.isSymm_diagonal _⟩
  · rw [isUnit_iff_ne_zero]
    show (Matrix.diagonal ![3, 3, 2] : Matrix (Fin 3) (Fin 3) ℚ).det ≠ 0
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    norm_num [Matrix.cons_val_two]
  · rw [replacementAtPi_schur]
    norm_num

/-- **The `S_{3,3}` values at `P_i` (`C = V_i`).** -/
theorem replacementAtPi_values :
    replacementAtPi.g = 2 / 3 ∧ replacementAtPi.mu = 0 ∧ replacementAtPi.h = 2 / 3 ∧
    replacementAtPi.eta = 2 / 3 ∧ replacementAtPi.alpha = 0 ∧ replacementAtPi.tau = 1 ∧
    replacementAtPi.ell = 1 / 3 ∧ replacementAtPi.lambda0 = ![1 / 3, 1 / 3, 0] := by
  have hg : replacementAtPi.g = 2 / 3 := by
    show replacementAtPi.schurScalar⁻¹ = 2 / 3
    rw [replacementAtPi_schur]
    norm_num
  have hmu : replacementAtPi.mu = 0 := by
    show replacementAtPi.g * (replacementAtPi.b - 2 + replacementAtPi.v ⬝ᵥ replacementAtPi.theta) = 0
    rw [hg, replacementAtPi_theta]
    show (2 / 3 : ℚ) * (2 - 2 + ![0, 0, 1] ⬝ᵥ ![1 / 3, 1 / 3, 0]) = 0
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
  have hh : replacementAtPi.h = 2 / 3 := by
    show replacementAtPi.r ⬝ᵥ replacementAtPi.u = 2 / 3
    rw [replacementAtPi_u]
    show ![1, 1, 0] ⬝ᵥ ![1 / 3, 1 / 3, 0] = (2 / 3 : ℚ)
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
  have heta : replacementAtPi.eta = 2 / 3 := by
    show replacementAtPi.r ⬝ᵥ replacementAtPi.theta = 2 / 3
    rw [replacementAtPi_theta]
    show ![1, 1, 0] ⬝ᵥ ![1 / 3, 1 / 3, 0] = (2 / 3 : ℚ)
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
  have halpha : replacementAtPi.alpha = 0 := by
    show replacementAtPi.v ⬝ᵥ replacementAtPi.u = 0
    rw [replacementAtPi_u]
    show ![0, 0, 1] ⬝ᵥ ![1 / 3, 1 / 3, 0] = (0 : ℚ)
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
  have htau : replacementAtPi.tau = 1 := by
    show replacementAtPi.m + replacementAtPi.alpha = 1
    rw [halpha]
    show (1 : ℚ) + 0 = 1
    norm_num
  have hell : replacementAtPi.ell = 1 / 3 := by
    show 1 - replacementAtPi.eta - replacementAtPi.tau * replacementAtPi.mu = 1 / 3
    rw [heta, htau, hmu]
    norm_num
  have hlam : replacementAtPi.lambda0 = ![1 / 3, 1 / 3, 0] := by
    show replacementAtPi.theta + replacementAtPi.mu • (replacementAtPi.M⁻¹ *ᵥ replacementAtPi.v) = _
    rw [replacementAtPi_theta, hmu]
    simp
  exact ⟨hg, hmu, hh, heta, halpha, htau, hell, hlam⟩

/-- The packaged statement applies to the `P_i` data. -/
theorem replacementAtPi_conclusion :
    replacementAtPi.blockMatrix *ᵥ replacementAtPi.lambda = replacementAtPi.qVector ∧
      1 - replacementAtPi.pVector ⬝ᵥ replacementAtPi.lambda = replacementAtPi.ell :=
  replacementAtPi.u_replacement_notation replacementAtPi_hypotheses.1
    replacementAtPi_hypotheses.2.1 replacementAtPi_hypotheses.2.2

/-- Block data at `P_i` with `C = B` (a weight-three component); `D₀ = (F_i, U_i, V_i)`. -/
def replacementAtB : ReplacementData (Fin 3) ℚ where
  b := 3
  v := ![0, 0, 0]
  M := !![3, 0, 0; 0, 2, -1; 0, -1, 2]
  q0 := ![1, 0, 0]
  m := 1
  r := ![1, 0, 1]

/-- The inverse of the `(F_i, U_i, V_i)` block. -/
def replacementAtB_Minv : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1 / 3, 0, 0; 0, 2 / 3, 1 / 3; 0, 1 / 3, 2 / 3]

theorem replacementAtB_M_inv : replacementAtB.M⁻¹ = replacementAtB_Minv := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [replacementAtB, replacementAtB_Minv, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.cons_val_two]

theorem replacementAtB_theta : replacementAtB.theta = ![1 / 3, 0, 0] := by
  show replacementAtB.M⁻¹ *ᵥ ![1, 0, 0] = _
  rw [replacementAtB_M_inv]
  funext i
  fin_cases i <;> norm_num [replacementAtB_Minv, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two]

theorem replacementAtB_u : replacementAtB.u = ![1 / 3, 1 / 3, 2 / 3] := by
  show replacementAtB.M⁻¹ *ᵥ ![1, 0, 1] = _
  rw [replacementAtB_M_inv]
  funext i
  fin_cases i <;> norm_num [replacementAtB_Minv, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two]

theorem replacementAtB_schur : replacementAtB.schurScalar = 3 := by
  show (3 : ℚ) - ![0, 0, 0] ⬝ᵥ (replacementAtB.M⁻¹ *ᵥ ![0, 0, 0]) = 3
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem replacementAtB_hypotheses :
    IsUnit replacementAtB.M.det ∧ replacementAtB.schurScalar ≠ 0 ∧ replacementAtB.M.IsSymm := by
  refine ⟨?_, ?_, Matrix.IsSymm.ext fun i j => ?_⟩
  · rw [isUnit_iff_ne_zero]
    show (!![3, 0, 0; 0, 2, -1; 0, -1, 2] : Matrix (Fin 3) (Fin 3) ℚ).det ≠ 0
    rw [Matrix.det_fin_three]
    norm_num [replacementAtB, Matrix.cons_val_two]
  · rw [replacementAtB_schur]
    norm_num
  · fin_cases i <;> fin_cases j <;> rfl

/-- **The `S_{3,3}` values at `P_i` with `C = B`:** `μ = 1/3` but `h = 1 > η = 1/3`. -/
theorem replacementAtB_values :
    replacementAtB.g = 1 / 3 ∧ replacementAtB.mu = 1 / 3 ∧ replacementAtB.h = 1 ∧
    replacementAtB.eta = 1 / 3 ∧ replacementAtB.alpha = 0 ∧ replacementAtB.tau = 1 ∧
    replacementAtB.ell = 1 / 3 ∧ replacementAtB.lambda0 = ![1 / 3, 0, 0] := by
  have hg : replacementAtB.g = 1 / 3 := by
    show replacementAtB.schurScalar⁻¹ = 1 / 3
    rw [replacementAtB_schur]
    norm_num
  have hmu : replacementAtB.mu = 1 / 3 := by
    show replacementAtB.g * (replacementAtB.b - 2 + replacementAtB.v ⬝ᵥ replacementAtB.theta) = 1 / 3
    rw [hg, replacementAtB_theta]
    show (1 / 3 : ℚ) * (3 - 2 + ![0, 0, 0] ⬝ᵥ ![1 / 3, 0, 0]) = 1 / 3
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
  have hh : replacementAtB.h = 1 := by
    show replacementAtB.r ⬝ᵥ replacementAtB.u = 1
    rw [replacementAtB_u]
    show ![1, 0, 1] ⬝ᵥ ![1 / 3, 1 / 3, 2 / 3] = (1 : ℚ)
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
  have heta : replacementAtB.eta = 1 / 3 := by
    show replacementAtB.r ⬝ᵥ replacementAtB.theta = 1 / 3
    rw [replacementAtB_theta]
    show ![1, 0, 1] ⬝ᵥ ![1 / 3, 0, 0] = (1 / 3 : ℚ)
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
  have halpha : replacementAtB.alpha = 0 := by
    show replacementAtB.v ⬝ᵥ replacementAtB.u = 0
    rw [replacementAtB_u]
    show ![0, 0, 0] ⬝ᵥ ![1 / 3, 1 / 3, 2 / 3] = (0 : ℚ)
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
  have htau : replacementAtB.tau = 1 := by
    show replacementAtB.m + replacementAtB.alpha = 1
    rw [halpha]
    show (1 : ℚ) + 0 = 1
    norm_num
  have hell : replacementAtB.ell = 1 / 3 := by
    show 1 - replacementAtB.eta - replacementAtB.tau * replacementAtB.mu = 1 / 3
    rw [heta, htau, hmu]
    norm_num
  have hMv : replacementAtB.M⁻¹ *ᵥ replacementAtB.v = 0 := by
    show replacementAtB.M⁻¹ *ᵥ ![0, 0, 0] = 0
    rw [show (![0, 0, 0] : Fin 3 → ℚ) = 0 from by funext i; fin_cases i <;> rfl, Matrix.mulVec_zero]
  have hlam : replacementAtB.lambda0 = ![1 / 3, 0, 0] := by
    show replacementAtB.theta + replacementAtB.mu • (replacementAtB.M⁻¹ *ᵥ replacementAtB.v) = _
    rw [replacementAtB_theta, hMv, smul_zero, add_zero]
  exact ⟨hg, hmu, hh, heta, halpha, htau, hell, hlam⟩

/-! ### U-KLT-COEFFICIENTS -/

/-- The `(3, 2)` chain is positive definite: `xᵀAx = (x₀ - x₁)² + 2x₀² + x₁²`. -/
theorem chainThreeTwo_posDef : chainThreeTwo.PosDef := by
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun x hx => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [chainThreeTwo]
  · have hq : star x ⬝ᵥ (chainThreeTwo *ᵥ x) = (x 0 - x 1) ^ 2 + 2 * x 0 ^ 2 + x 1 ^ 2 := by
      simp [chainThreeTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hq]
    have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    rcases hne with h | h
    · have : 0 < x 0 ^ 2 := by positivity
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1)]
    · have : 0 < x 1 ^ 2 := by positivity
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0)]

/-- The nonzero solution of the `(3, 2)` chain equation. -/
theorem chainThreeTwo_nonzero_solution :
    chainThreeTwo *ᵥ ![2 / 5, 1 / 5] = canonicalRightHandSide ![3, 2] ∧
      (![2 / 5, 1 / 5] : Fin 2 → ℚ) ≠ 0 := by
  refine ⟨by rw [chainThreeTwo_rhs]; exact chainThreeTwo_mulVec, ?_⟩
  intro h
  have := congr_fun h 1
  norm_num at this

/-- The all-weight-two `A₂` block. -/
def a2Block : Matrix (Fin 2) (Fin 2) ℚ := !![2, -1; -1, 2]

theorem a2Block_posDef : a2Block.PosDef := by
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun x hx => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [a2Block]
  · have hq : star x ⬝ᵥ (a2Block *ᵥ x) = (x 0 - x 1) ^ 2 + x 0 ^ 2 + x 1 ^ 2 := by
      simp [a2Block, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hq]
    have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    rcases hne with h | h
    · have : 0 < x 0 ^ 2 := by positivity
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1)]
    · have : 0 < x 1 ^ 2 := by positivity
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0)]

/-- The all-weight-two clause applies to the `A₂` block. -/
theorem a2Block_coefficients_zero (lam : Fin 2 → ℚ)
    (h : a2Block *ᵥ lam = canonicalRightHandSide ![2, 2]) : lam = 0 :=
  coefficients_eq_zero_of_allWeightTwo a2Block_posDef (fun i => by fin_cases i <;> rfl) h

/-! ### U-HIGHER-RESOLUTIONS: a three-step tower -/

/-- Node of coefficients `1/2, 1/3`, then a smooth point on the new exceptional
curve (coefficient `-1/6`), then a point outside the boundary. -/
def towerCenters : List (BlowupCenter ℚ) :=
  [BlowupCenter.node (1 / 2) (1 / 3), BlowupCenter.smooth (-1 / 6), BlowupCenter.outside]

/-- The resulting coefficient list. -/
def towerResult : List ℚ :=
  towerCenters.foldl (fun acc c => exceptionalCoefficient c :: acc) [1 / 2, 1 / 3]

theorem towerResult_eq : towerResult = [-1, -7 / 6, -1 / 6, 1 / 2, 1 / 3] := by
  norm_num [towerResult, towerCenters, exceptionalCoefficient]

theorem towerResult_lt_one : ∀ x ∈ towerResult, x < 1 :=
  tower_coefficients_lt_one towerCenters [1 / 2, 1 / 3]
    (by norm_num [List.forall_mem_cons])
    (by norm_num [towerCenters, List.forall_mem_cons, BlowupCenter.coefficients])

/-! ### U-NEF-POSITIVE-SPAN: `m = 2` -/

theorem nef_positive_span_m_two :
    (cpGram 2).det = -2 ∧ (cpGram ((2 : ℕ) : ℤ)).det < 0 ∧ cpSquare 2 1 1 = 1 := by
  refine ⟨?_, (cpGram_det_neg_iff 2).mpr le_rfl, ?_⟩
  · rw [cpGram_det]; norm_num
  · decide

/-! ### U-PICARD-PARITY and U-CODE-KERNEL-LIFT: the lattice `I_{1,5}` -/

namespace I15

/-- Diagonal of the odd unimodular form `⟨1⟩ ⊕ ⟨-1⟩^5` on `ℤ^6` (basis `h, e₁, …, e₅`). -/
def d : Fin 6 → ℤ := ![1, -1, -1, -1, -1, -1]

/-- The Gram matrix. -/
def gram : Matrix (Fin 6) (Fin 6) ℤ := Matrix.diagonal d

/-- The identity of `ℤ^6`, as a linear equivalence from the `Pi.module` structure to the
canonical `ℤ`-module structure of the additive group (the structure used by the accepted
lattice theorems). Keeping every object on the canonical structure makes the final
instantiation syntactic; the accepted `EQUALITY_NUMBERS` note records that unifying the two
structures through `BilinForm.toMatrix` at `Fin 6` exceeds the elaborator's recursion limit. -/
def toIntEquiv : @LinearEquiv ℤ ℤ _ _ (RingHom.id ℤ) (RingHom.id ℤ) _ _ (Fin 6 → ℤ) (Fin 6 → ℤ)
    _ _ (Pi.module (Fin 6) (fun _ => ℤ) ℤ) (AddCommGroup.toIntModule (Fin 6 → ℤ)) where
  toFun := id
  invFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bilinear form on the `Pi.module` structure. -/
def B₀ : LinearMap.BilinForm ℤ (Fin 6 → ℤ) := Matrix.toBilin' gram

/-- The same form on the canonical module structure. -/
def B := B₀.comp toIntEquiv.symm.toLinearMap toIntEquiv.symm.toLinearMap

theorem B_apply (x y : Fin 6 → ℤ) : B x y = x ⬝ᵥ (gram *ᵥ y) :=
  Matrix.toBilin'_apply' gram x y

/-- The standard basis, carried to the canonical module structure. -/
noncomputable def b := (Pi.basisFun ℤ (Fin 6)).map toIntEquiv

/-- The characteristic vector `K = -3h + Σ e_i`. -/
def K : Fin 6 → ℤ := ![-3, 1, 1, 1, 1, 1]

/-- Four pairwise orthogonal vectors of square `-2` orthogonal to `K`:
`e₁ - e₂`, `h - e₁ - e₂ - e₃`, `e₄ - e₅`, `h - e₃ - e₄ - e₅`. -/
def w : Fin 4 → (Fin 6 → ℤ) :=
  ![![0, 1, -1, 0, 0, 0], ![1, -1, -1, -1, 0, 0], ![0, 0, 0, 0, 1, -1], ![1, 0, 0, -1, -1, -1]]

/-- Half of their sum: `m = h - e₂ - e₃ - e₅`. -/
def m : Fin 6 → ℤ := ![1, 0, -1, -1, 0, -1]

theorem hsq : ∀ i, B (w i) (w i) = -2 := by
  simp only [B_apply]
  decide

theorem horth : ∀ i j, i ≠ j → B (w i) (w j) = 0 := by
  simp only [B_apply]
  decide

theorem hK : ∀ i, B K (w i) = 0 := by
  simp only [B_apply]
  decide

theorem hm : (2 : ℤ) • m = ∑ i, w i := by
  funext k
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  fin_cases k <;>
    norm_num [m, w, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, cons_val_five]

/-- `K` is characteristic: `B x x - B K x = x₀(x₀+1) + 2x₀ - Σ_{i≥1} x_i(x_i - 1)`. -/
theorem hchar : @KltDP.Codes.IsCharacteristic (Fin 6 → ℤ) _ (AddCommGroup.toIntModule _) B K := by
  intro x
  rw [B_apply, B_apply]
  have key : x ⬝ᵥ (gram *ᵥ x) - K ⬝ᵥ (gram *ᵥ x) =
      (x 0 * (x 0 + 1) + 2 * x 0) -
        (x 1 * (x 1 - 1) + x 2 * (x 2 - 1) + x 3 * (x 3 - 1) + x 4 * (x 4 - 1) +
          x 5 * (x 5 - 1)) := by
    simp [gram, d, K, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_six, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, cons_val_five]
    ring
  rw [key, even_iff_two_dvd]
  have h0 : (2 : ℤ) ∣ x 0 * (x 0 + 1) := even_iff_two_dvd.mp (Int.even_mul_succ_self _)
  have hp : ∀ k : Fin 6, (2 : ℤ) ∣ x k * (x k - 1) :=
    fun k => even_iff_two_dvd.mp (Int.even_mul_pred_self _)
  exact dvd_sub (dvd_add h0 (dvd_mul_right 2 _))
    (dvd_add (dvd_add (dvd_add (dvd_add (hp 1) (hp 2)) (hp 3)) (hp 4)) (hp 5))

/-- **U-PICARD-PARITY witness.** -/
theorem picard_parity :
    B K m = 0 ∧ 2 * B m m = -(Fintype.card (Fin 4) : ℤ) ∧ 4 ∣ Fintype.card (Fin 4) :=
  u_picard_parity B K hchar w m hsq horth hK hm

/-- The Gram matrix of `B` in the basis `b` is `gram`. -/
theorem toMatrix_b : BilinForm.toMatrix b B = gram := by
  ext i j
  rw [_root_.BilinForm.toMatrix_apply, b, Basis.map_apply, Basis.map_apply, Pi.basisFun_apply,
    Pi.basisFun_apply]
  show B₀ (Pi.single i 1) (Pi.single j 1) = gram i j
  rw [B₀, Matrix.toBilin'_apply', single_dotProduct, one_mul, Matrix.mulVec_single_one,
    Matrix.transpose_apply]

/-- Unimodularity: `det gram = -1`. -/
theorem hB : (BilinForm.toMatrix b B).det.natAbs = 1 := by
  rw [toMatrix_b, gram, Matrix.det_diagonal, Fin.prod_univ_six]
  decide

/-- Reduction of the three independent node pairings modulo two. -/
def parityMap : (Fin 6 → ℤ) →+ (Fin 3 → ZMod 2) where
  toFun y := ![((y 1 + y 2 : ℤ) : ZMod 2), ((y 0 + y 1 + y 2 + y 3 : ℤ) : ZMod 2),
    ((y 4 + y 5 : ℤ) : ZMod 2)]
  map_zero' := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_two]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_two] <;> ring

theorem parityMap_surjective : Function.Surjective parityMap := by
  intro t
  refine ⟨![(((t 1 - t 0).val : ℕ) : ℤ), (((t 0).val : ℕ) : ℤ), 0, 0, (((t 2).val : ℕ) : ℤ), 0], ?_⟩
  funext i
  fin_cases i <;>
    simp [parityMap, ZMod.natCast_zmod_val, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, cons_val_five]

/-- `Γ`: the vectors pairing evenly with every node (canonical module structure). -/
def Γ := LinearMap.ker parityMap.toIntLinearMap

theorem Γ_toAddSubgroup : Γ.toAddSubgroup = parityMap.ker := by
  rw [Γ, LinearMap.ker_toAddSubgroup]
  congr 1

theorem Γ_index : Γ.toAddSubgroup.index = 8 := by
  rw [Γ_toAddSubgroup, AddSubgroup.index_eq_card,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective parityMap
      parityMap_surjective).toEquiv,
    Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_zmod]
  norm_num

instance Γ_finiteIndex : Γ.toAddSubgroup.FiniteIndex :=
  ⟨by rw [Γ_index]; decide⟩

theorem Γ_index_factorization : Γ.toAddSubgroup.index.factorization 2 = 3 := by
  rw [Γ_index, show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.prime_two.factorization_pow]
  simp

theorem pair0 (y : Fin 6 → ℤ) : w 0 ⬝ᵥ (gram *ᵥ y) = (y 1 + y 2) - 2 * y 1 := by
  simp [w, gram, d, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_six, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_val_five]
  ring

theorem pair1 (y : Fin 6 → ℤ) : w 1 ⬝ᵥ (gram *ᵥ y) = y 0 + y 1 + y 2 + y 3 := by
  simp [w, gram, d, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_six, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_val_five]

theorem pair2 (y : Fin 6 → ℤ) : w 2 ⬝ᵥ (gram *ᵥ y) = (y 4 + y 5) - 2 * y 4 := by
  simp [w, gram, d, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_six, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_val_five]
  ring

theorem pair3 (y : Fin 6 → ℤ) :
    w 3 ⬝ᵥ (gram *ᵥ y) = ((y 0 + y 1 + y 2 + y 3) - (y 1 + y 2)) + (y 4 + y 5) := by
  simp [w, gram, d, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_six, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_val_five]
  ring

/-- Every node pairs evenly with `Γ`. -/
theorem hpair : ∀ i y, y ∈ Γ → Even (B (w i) y) := by
  intro i y hy
  have hy' : parityMap.toIntLinearMap y = 0 := LinearMap.mem_ker.mp hy
  have h0 : ((y 1 + y 2 : ℤ) : ZMod 2) = 0 := congr_fun hy' 0
  have h1 : ((y 0 + y 1 + y 2 + y 3 : ℤ) : ZMod 2) = 0 := congr_fun hy' 1
  have h2 : ((y 4 + y 5 : ℤ) : ZMod 2) = 0 := congr_fun hy' 2
  have d12 : (2 : ℤ) ∣ y 1 + y 2 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (y 1 + y 2) 2).mp h0
    exact_mod_cast this
  have d0123 : (2 : ℤ) ∣ y 0 + y 1 + y 2 + y 3 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (y 0 + y 1 + y 2 + y 3) 2).mp h1
    exact_mod_cast this
  have d45 : (2 : ℤ) ∣ y 4 + y 5 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (y 4 + y 5) 2).mp h2
    exact_mod_cast this
  rw [B_apply, even_iff_two_dvd]
  match i with
  | 0 => rw [pair0]; exact dvd_sub d12 (dvd_mul_right 2 _)
  | 1 => rw [pair1]; exact d0123
  | 2 => rw [pair2]; exact dvd_sub d45 (dvd_mul_right 2 _)
  | 3 => rw [pair3]; exact dvd_add (dvd_sub d0123 d12) d45

theorem hcard : Γ.toAddSubgroup.index.factorization 2 < Fintype.card (Fin 4) := by
  rw [Γ_index_factorization]
  norm_num

/-- **U-CODE-KERNEL-LIFT witness.** All hypotheses hold and the conclusion is an
actual integral half-sum. -/
theorem code_kernel_lift :
    ∃ J : Finset (Fin 4), J.Nonempty ∧ ∃ m : Fin 6 → ℤ, (2 : ℤ) • m = ∑ i ∈ J, w i :=
  u_code_kernel_lift b B hB Γ w hpair hcard

theorem code_kernel_lift_four :
    ∃ J : Finset (Fin 4), J.Nonempty ∧ 4 ∣ J.card ∧ 4 ≤ J.card ∧
      ∃ m : Fin 6 → ℤ, (2 : ℤ) • m = ∑ i ∈ J, w i :=
  u_code_kernel_lift_four b B hB Γ w hpair hcard K hchar hsq horth hK

end I15

/-! ### A `WeightedForest`, an admissible `Contact` -/

/-- The leaf-rooted three-leaf star (accepted `rootedBlockGraph .leafStar`), root weight
three, leaves weight two, marks at the root and two leaves. -/
def leafStarForest : WeightedForest (RootedBlockVertex .leafStar) where
  graph := rootedBlockGraph .leafStar
  decAdj := inferInstance
  weight := Sum.elim (fun _ : Unit => 3) (fun _ : Fin 3 => 2)
  two_le_weight := by
    intro v
    rcases v with a | b <;> simp
  acyclic := (rootedTrees_listed_isTree .leafStar).IsAcyclic
  mark := ![Sum.inl (), Sum.inr 0, Sum.inr 1]
  mark_injective := by decide

theorem leafStarForest_card : Fintype.card (KltDP.LinearAlgebra.RootedBlockVertex .leafStar) = 4 := by
  decide

/-- `P 0` is an admissible contact (accepted `EqualityContacts`). -/
theorem contact_P0_admissible : (KltDP.EqualityContacts.P 0).Admissible := by
  decide

/-! ### Remaining hypothesis instances -/

theorem frobenius_three_three :
    KltDP.Examples.FrobeniusArithmetic.integerNumerator 3 3 = 1 ∧
      (0 < KltDP.Examples.FrobeniusArithmetic.integerNumerator 3 3 ↔ 3 = 2 ∨ 3 = 3 ∧ 3 = 3) :=
  ⟨by decide, (u_frobenius_sign Nat.prime_three le_rfl).1⟩

theorem core_weights_three_four :
    ((3 : ℚ) - 2) / 3 + ((4 : ℚ) - 2) / 4 < 1 ∧
      (min 3 4 = 3 ∧ (max 3 4 = 3 ∨ max 3 4 = 4 ∨ max 3 4 = 5)) :=
  ⟨by norm_num, u_core_weights.1 3 4 (by norm_num) (by norm_num) (by norm_num)⟩

theorem section_count_three :
    ((3 : ℕ) : ℤ) + ∑ t ∈ insert (0 : Fin 4) ({1} ∪ {2, 3}), (![-1, -1, 1, 1] : Fin 4 → ℤ) t - 0 ≤
      ((3 : ℕ) : ℤ) + 1 :=
  section_count_le_succ 3 (by norm_num) 0 {1} {2, 3} ![-1, -1, 1, 1] 0 le_rfl
    (by decide) (by decide) (Finset.disjoint_singleton_left.mpr (by decide))
    (by decide) (by decide) (by decide) (by decide)

theorem graph_bridge_three :
    (∀ i ∈ (Finset.univ : Finset (Fin 1)), (0 : ℚ) ≤ (fun _ : Fin 1 => (1 / 3 : ℚ)) i *
      (fun _ : Fin 1 => (1 : ℚ)) i) ∧
    (∑ i ∈ (Finset.univ : Finset (Fin 1)), (fun _ : Fin 1 => (1 / 3 : ℚ)) i *
      (fun _ : Fin 1 => (1 : ℚ)) i < 1) ∧
    (3 : ℕ) ≤ 3 :=
  ⟨fun _ _ => by norm_num, by norm_num [Fin.sum_univ_one],
    weight_le_three (Finset.univ : Finset (Fin 1)) (fun _ => 1 / 3) (fun _ => 1)
      (fun _ _ => by norm_num) (by norm_num [Fin.sum_univ_one]) (0 : Fin 1) (Finset.mem_univ 0) 3
      (by norm_num) (by norm_num) (by norm_num)⟩

theorem average_descent_two :
    ∃ i ∈ (Finset.univ : Finset (Fin 2)),
      (![1, 3] : Fin 2 → ℚ) i ≤ (∑ j ∈ Finset.univ, ((fun _ => (1 : ℕ)) j : ℚ) * (![1, 3] : Fin 2 → ℚ) j + 0) / 2 :=
  u_average_descent Finset.univ (fun _ => 1) (fun _ _ => le_rfl) (by simp) ![1, 3]
    (fun i _ => by fin_cases i <;> norm_num) 0 le_rfl

theorem effective_support_negDef : (-(-chainThreeTwo)).PosDef := by
  rw [neg_neg]
  exact chainThreeTwo_posDef

theorem count_change_values :
    countChange 1 2 = -1 ∧ countChange 1 0 = 0 ∧ countChange 0 0 = -1 ∧ countChange 3 1 = 2 := by
  decide

theorem single_effective_beta_three : coreT ⬝ᵥ (coreGram 3 *ᵥ coreT) = 0 := by
  rw [coreT_square]
  norm_num

end SupportNonvacuity

open SupportNonvacuity in
/-- **Support nonvacuity bundle.** The hypotheses of the reviewed Support modules are
jointly satisfiable by the explicit finite data of this module. -/
theorem support_nonvacuity :
    (IsUnit replacementAtPi.M.det ∧ replacementAtPi.schurScalar ≠ 0 ∧ replacementAtPi.M.IsSymm ∧
      replacementAtPi.mu = 0 ∧ replacementAtPi.h = 2 / 3 ∧ replacementAtPi.eta = 2 / 3 ∧
      replacementAtPi.ell = 1 / 3) ∧
    (replacementAtB.mu = 1 / 3 ∧ replacementAtB.h = 1 ∧ replacementAtB.eta = 1 / 3 ∧
      replacementAtB.ell = 1 / 3) ∧
    (chainThreeTwo.PosDef ∧ (![2 / 5, 1 / 5] : Fin 2 → ℚ) ≠ 0 ∧
      chainThreeTwo *ᵥ ![2 / 5, 1 / 5] = canonicalRightHandSide ![3, 2] ∧ a2Block.PosDef) ∧
    (towerResult = [-1, -7 / 6, -1 / 6, 1 / 2, 1 / 3] ∧ ∀ x ∈ towerResult, x < 1) ∧
    ((cpGram 2).det = -2 ∧ cpSquare 2 1 1 = 1) ∧
    (@KltDP.Codes.IsCharacteristic (Fin 6 → ℤ) _ (AddCommGroup.toIntModule _) I15.B I15.K ∧
      (∀ i, I15.B (I15.w i) (I15.w i) = -2) ∧
      (2 : ℤ) • I15.m = ∑ i, I15.w i ∧
      (BilinForm.toMatrix I15.b I15.B).det.natAbs = 1 ∧
      I15.Γ.toAddSubgroup.index = 8 ∧
      ∃ J : Finset (Fin 4), J.Nonempty ∧ ∃ m : Fin 6 → ℤ, (2 : ℤ) • m = ∑ i ∈ J, I15.w i) ∧
    (KltDP.EqualityContacts.P 0).Admissible ∧
    Fintype.card (KltDP.LinearAlgebra.RootedBlockVertex .leafStar) = 4 ∧
    countChange 1 2 = -1 :=
  ⟨⟨replacementAtPi_hypotheses.1, replacementAtPi_hypotheses.2.1, replacementAtPi_hypotheses.2.2,
      replacementAtPi_values.2.1, replacementAtPi_values.2.2.1, replacementAtPi_values.2.2.2.1,
      replacementAtPi_values.2.2.2.2.2.2.1⟩,
    ⟨replacementAtB_values.2.1, replacementAtB_values.2.2.1, replacementAtB_values.2.2.2.1,
      replacementAtB_values.2.2.2.2.2.2.1⟩,
    ⟨chainThreeTwo_posDef, chainThreeTwo_nonzero_solution.2, chainThreeTwo_nonzero_solution.1,
      a2Block_posDef⟩,
    ⟨towerResult_eq, towerResult_lt_one⟩,
    ⟨nef_positive_span_m_two.1, nef_positive_span_m_two.2.2⟩,
    ⟨I15.hchar, I15.hsq, I15.hm, I15.hB, I15.Γ_index, I15.code_kernel_lift⟩,
    contact_P0_admissible, leafStarForest_card, count_change_values.1⟩

end KltDP.Support
