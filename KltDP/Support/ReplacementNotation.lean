import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-!
# Support obligation U-REPLACEMENT-NOTATION: block data and signs for the one-component replacement

Manuscript `source/manuscript.tex` lines 954–988 (§4, "Replacing one exceptional
component"). With `D = C + D_0`, the positive intersection matrix, canonical-degree
vector and contact vector are ordered as
`A = [[b, -vᵀ], [-v, M]]`, `q = (b - 2, q_0)`, `p = (m, r)`, and the scalars
`g = (b - vᵀM⁻¹v)⁻¹`, `θ = M⁻¹q_0`, `u = M⁻¹r`, `μ = g(b - 2 + vᵀθ)`, `h = rᵀu`,
`η = rᵀθ`, `α = vᵀu`, `τ = m + α`, `ℓ = 1 - η - τμ` are defined, with
`λ_0 = θ + μM⁻¹v` the original coefficient vector on `D_0`.

This module records these definitions verbatim as functions of the block data
and proves the two algebraic facts the manuscript uses implicitly:

* `(μ, λ_0)` solves the full row equation `A λ = q` (so `μ` is the coefficient of
  `C` and `λ_0` the restricted coefficient vector, whenever `M` is invertible and
  the Schur scalar `b - vᵀM⁻¹v` is nonzero);
* `1 - pᵀλ = ℓ` when `M` is symmetric, i.e. the displayed value of `ℓ` is exactly
  `1 - pᵀλ`; the geometric identity `L·P = 1 - pᵀλ` for a `(-1)`-curve `P`
  (Lemma 2.5, `eq:minus-one-degree`) is a separate obligation.

No surface, curve or intersection number is constructed here.
-/

noncomputable section

namespace KltDP.Support

open Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [Field 𝕜]

/-- The block data of the one-component replacement: `C² = -b`, contact column
`v` of `C` with `D_0`, the block `M` of `D_0`, its canonical-degree vector `q_0`,
`m = P·C` and the contact vector `r` of `P` with `D_0`. -/
structure ReplacementData (ι 𝕜 : Type*) where
  b : 𝕜
  v : ι → 𝕜
  M : Matrix ι ι 𝕜
  q0 : ι → 𝕜
  m : 𝕜
  r : ι → 𝕜

namespace ReplacementData

variable (d : ReplacementData ι 𝕜)

/-- `A = [[b, -vᵀ], [-v, M]]`, with `C` indexed by `Unit` first. -/
def blockMatrix : Matrix (Unit ⊕ ι) (Unit ⊕ ι) 𝕜 :=
  fromBlocks (of fun _ _ => d.b) (of fun _ j => -d.v j) (of fun i _ => -d.v i) d.M

/-- `q = (b - 2, q_0)`. -/
def qVector : Unit ⊕ ι → 𝕜 := Sum.elim (fun _ => d.b - 2) d.q0

/-- `p = (m, r)`. -/
def pVector : Unit ⊕ ι → 𝕜 := Sum.elim (fun _ => d.m) d.r

/-- The Schur scalar `b - vᵀM⁻¹v`, whose inverse is `g`. -/
def schurScalar : 𝕜 := d.b - d.v ⬝ᵥ (d.M⁻¹ *ᵥ d.v)

/-- `g = (b - vᵀM⁻¹v)⁻¹`. -/
def g : 𝕜 := (d.schurScalar)⁻¹

/-- `θ = M⁻¹q_0`. -/
def theta : ι → 𝕜 := d.M⁻¹ *ᵥ d.q0

/-- `u = M⁻¹r`. -/
def u : ι → 𝕜 := d.M⁻¹ *ᵥ d.r

/-- `μ = g(b - 2 + vᵀθ)`. -/
def mu : 𝕜 := d.g * (d.b - 2 + d.v ⬝ᵥ d.theta)

/-- `h = rᵀu`. -/
def h : 𝕜 := d.r ⬝ᵥ d.u

/-- `η = rᵀθ`. -/
def eta : 𝕜 := d.r ⬝ᵥ d.theta

/-- `α = vᵀu`. -/
def alpha : 𝕜 := d.v ⬝ᵥ d.u

/-- `τ = m + α`. -/
def tau : 𝕜 := d.m + d.alpha

/-- `ℓ = 1 - η - τμ`. -/
def ell : 𝕜 := 1 - d.eta - d.tau * d.mu

/-- `λ_0 = θ + μ M⁻¹v`, the original coefficient vector on `D_0`. -/
def lambda0 : ι → 𝕜 := d.theta + d.mu • (d.M⁻¹ *ᵥ d.v)

/-- The full coefficient vector `λ = (μ, λ_0)`. -/
def lambda : Unit ⊕ ι → 𝕜 := Sum.elim (fun _ => d.mu) d.lambda0

theorem mu_mul_schurScalar (hg : d.schurScalar ≠ 0) :
    d.mu * d.schurScalar = d.b - 2 + d.v ⬝ᵥ d.theta := by
  unfold mu g
  rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hg, one_mul]

theorem M_mulVec_theta (hM : IsUnit d.M.det) : d.M *ᵥ d.theta = d.q0 := by
  unfold theta
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv d.M hM, one_mulVec]

theorem M_mulVec_inv_v (hM : IsUnit d.M.det) : d.M *ᵥ (d.M⁻¹ *ᵥ d.v) = d.v := by
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv d.M hM, one_mulVec]

/-- **The block data solve the row equation.** `(μ, λ_0)` satisfies `A λ = q`. -/
theorem blockMatrix_mulVec_lambda (hM : IsUnit d.M.det) (hg : d.schurScalar ≠ 0) :
    d.blockMatrix *ᵥ d.lambda = d.qVector := by
  unfold blockMatrix lambda qVector
  rw [fromBlocks_mulVec]
  have hcomp1 : (Sum.elim (fun _ : Unit => d.mu) d.lambda0 ∘ Sum.inl) = fun _ => d.mu := rfl
  have hcomp2 : (Sum.elim (fun _ : Unit => d.mu) d.lambda0 ∘ Sum.inr) = d.lambda0 := rfl
  rw [hcomp1, hcomp2]
  ext (x | i)
  · -- the `C` row: `b μ - vᵀ λ_0 = b - 2`
    simp only [Sum.elim_inl, Pi.add_apply, mulVec, dotProduct, of_apply, Finset.univ_unique,
      Finset.sum_singleton, neg_mul]
    unfold lambda0
    have hexp : ∑ j, -(d.v j * (d.theta + d.mu • d.M⁻¹ *ᵥ d.v) j) =
        -(d.v ⬝ᵥ d.theta) - d.mu * (d.v ⬝ᵥ (d.M⁻¹ *ᵥ d.v)) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum,
        ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hexp]
    have := d.mu_mul_schurScalar hg
    unfold schurScalar at this
    linear_combination this
  · -- the `D_0` rows: `-v μ + M λ_0 = q_0`
    simp only [Sum.elim_inr, Pi.add_apply]
    have h1 : (of fun i _ => -d.v i) *ᵥ (fun _ : Unit => d.mu) = fun i => -(d.v i * d.mu) := by
      ext i
      simp [mulVec, dotProduct, Finset.univ_unique, Finset.sum_singleton]
    have h2 : d.M *ᵥ d.lambda0 = d.q0 + d.mu • d.v := by
      unfold lambda0
      rw [mulVec_add, mulVec_smul, d.M_mulVec_theta hM, d.M_mulVec_inv_v hM]
    rw [h1, h2]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- `pᵀλ = mμ + rᵀλ_0`. -/
theorem pVector_dotProduct_lambda :
    d.pVector ⬝ᵥ d.lambda = d.m * d.mu + d.r ⬝ᵥ d.lambda0 := by
  unfold pVector lambda
  rw [sumElim_dotProduct_sumElim]
  simp [dotProduct, Finset.univ_unique, Finset.sum_singleton]

/-- With `M` symmetric, `rᵀM⁻¹v = vᵀM⁻¹r = α`. -/
theorem r_dotProduct_inv_v (hs : d.M.IsSymm) : d.r ⬝ᵥ (d.M⁻¹ *ᵥ d.v) = d.alpha := by
  unfold alpha u
  rw [dotProduct_mulVec, ← mulVec_transpose, Matrix.transpose_nonsing_inv, hs.eq,
    dotProduct_comm]

/-- **The displayed value of `ℓ`.** `1 - pᵀλ = 1 - η - τμ = ℓ` when `M` is symmetric. -/
theorem one_sub_pVector_dotProduct_lambda (hs : d.M.IsSymm) :
    1 - d.pVector ⬝ᵥ d.lambda = d.ell := by
  rw [d.pVector_dotProduct_lambda]
  unfold ell tau eta lambda0
  rw [dotProduct_add, dotProduct_smul, d.r_dotProduct_inv_v hs]
  simp only [smul_eq_mul]
  ring

/-- **U-REPLACEMENT-NOTATION**, arithmetic clause: the block data determine a
solution `(μ, λ_0)` of the row equation and `1 - pᵀλ = ℓ`. -/
theorem u_replacement_notation (hM : IsUnit d.M.det) (hg : d.schurScalar ≠ 0)
    (hs : d.M.IsSymm) :
    d.blockMatrix *ᵥ d.lambda = d.qVector ∧ 1 - d.pVector ⬝ᵥ d.lambda = d.ell :=
  ⟨d.blockMatrix_mulVec_lambda hM hg, d.one_sub_pVector_dotProduct_lambda hs⟩

end ReplacementData

end KltDP.Support

end
