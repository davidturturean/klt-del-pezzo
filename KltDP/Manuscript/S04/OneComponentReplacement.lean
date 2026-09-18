import KltDP.Manuscript.S04.ExcessContact
import KltDP.Manuscript.S02.SquareDegree
import KltDP.Manuscript.S02.NumericalContraction
import KltDP.LinearAlgebra.ReplacementScalars
import KltDP.LinearAlgebra.Stieltjes
import KltDP.Geometry.ResolutionContractionInduction
import KltDP.Geometry.ActualContractionMorphismDescent
import KltDP.Geometry.RegularTargetCanonicalDiscrepancy
import KltDP.Geometry.ActualExceptionalIncidence
import KltDP.Geometry.ActualExceptionalComponents
import KltDP.Geometry.SurfaceRegularityOnIsomorphismOpen
import KltDP.Geometry.ProperGenericPointSurjective
import KltDP.Geometry.PrimeCurveCodimension
import KltDP.Support.CountZeroContact
import KltDP.Support.WeightedForestCore
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Manuscript Theorem 4.5: replacement of one exceptional component

Source: `source/manuscript.tex`, lines 954–989 (block data) and 990–1111
(`thm:one-component-replacement`).

Fix a resolution datum `R`, an exceptional component `C` and an exterior `(-1)`-curve `P`
whose only excess contact is `C` (all contacts with `D₀ = D − C` are bounded), and assume that
`G† = P + D₀` is an SNC forest (the hypothesis `hacyclic`; the pairwise intersection bound
`≤ 1` is derived from the datum and Lemma 4.2, `pair_famG`). Writing
`A = [[b, -vᵀ], [-v, M]]`, `q = (b-2, q₀)`, `p = (m, r)` (eq:replacement-block-data), the
manuscript defines `g, θ, u, μ, h, η, α, τ, ℓ` (eq:replacement-scalars-1..3) and
`c = (1-η)/(1-h)`, `λ₀† = θ - c u` (eq:replacement-new-data). This module realises these
objects from the datum (`Replacement.Mblock`, `vvec`, `q0`, `rvec`, `theta`, `uvec`, ...),
with `μ = λ_C`, `λ₀ = λ|_{D₀}` and `ℓ = L·P` the *geometric* quantities, and proves, in the
manuscript's order:

* (i) the row equations in block form (`M_mulVec_lam0`, `lam0_eq`, `mu_mul_schur`), the
  positive Schur scalar `b - vᵀM⁻¹v > 0` (`schur_pos`), `M` positive definite Stieltjes, the
  energy identities `pᵀA⁻¹p = h + gτ²`, `pᵀλ = η + τμ`, `ℓ = 1 - η - τμ`
  (eq:replacement-old-energy), `0 ≤ h ≤ η < 1`, `-c < 1`, `0 ≤ λ₀† ≤ λ₀ < 1`
  (eq:replacement-coefficient-bounds) and the rank-one identity `(M - r rᵀ) λ₀† = q₀ - r`;
* (ii) the null equations `A† (λ₀†, -c) = q†` for the retained family `G†`
  (`negIntersectionMatrix_famG_mulVec_lamG`);
* (iii) for `L† = -(K_S + Σ λ†_j G†_j) ∈ N¹(S)_ℚ` (`Lnum'`): `(L†)² - L² = (1-η)²/(1-h) - μ²/g > 0`
  (eq:replacement-square-gain) and `L†·C = τ(1-η)/(1-h) - μ/g > 0` (eq:replacement-deleted-degree);
* (iv) `L†` is nef with null locus exactly `G†` (`degree_Lnum'_nonneg`, `degree_Lnum'_eq_zero_iff`),
  via eq:replacement-effective-difference `L† = L + μC + Σ(λ_i - λ†_i)D_i + cP`;
* (v) a Cartier multiple of `L†` (`exists_cartier_multiple`) and Theorem 2.6: `G†` is contracted
  to a rank-one klt del Pezzo surface `X†` with `K_S + Σ λ†_j G†_j = f^*K_{X†}`
  (`anticanonicalContraction_famG`);
* (vi) a resolution datum `R₁` of `X†` with `ρ(R₁.S) < ρ(R.S)` (the union's contraction
  induction down to a minimal resolution, each step lowering the exceptional count);
* (vii) the singular-point count `#Sing(X†) = #Sing(X) + countChange (deg C) a`, i.e.
  `s_C - a` for `a ≥ 1` and `s_C - 1` for `a = 0` (eq:replacement-component-count), with
  `s_C = deg_D C = #π₀(Γ - C)` (`card_components_induce_compl`) and `a = contactCount` the number
  of components of `D₀` met by `P`. The count is computed on the (non-minimal) resolution
  `f : S → X†`: the singular points are exactly the images of the retained components `D_i`
  (their discrepancies `-λ†_i ≤ 0`), and for `a = 0` the isolated contracted `P` is a regular
  point (`image_P_regular`, through the Castelnuovo contraction of `P`).

Main statement: `oneComponentReplacement_datum`. What is *not* proved here (the manuscript's
`ρ(S₁) = ρ(S) − 1` with `S₁ → X†` the minimal resolution obtained by blowing down `P`, lines
1030–1034 and 1089–1098): only the strict inequality `ρ(R₁.S) < ρ(R.S)` is delivered, which is
what Theorem 7.1 (lines 2400–2420) consumes.

The characteristic hypotheses `(p : ℕ) [CharP k p] (hp : 0 < p)` enter through Lemma 2.8's
identity `pᵀA⁻¹p > 1` (`rankOneProjection_green_gt_one`), Theorem 2.6 and the Picard-rank
formula `ρ(S) = ρ(X) + #D`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix TopologicalSpace
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript KltDP.Manuscript.S02

universe u

namespace KltDP.Manuscript.S04

namespace Replacement

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k) [DecidableEq R.Vertices]
  (C : R.Vertices) (P : R.S.PrimeCurve)

/-! ### Block data (manuscript eq:replacement-block-data, lines 954–968) -/

/-- The index type of `D₀ = D − C`. -/
abbrev D0 : Type u := {i : R.Vertices // i ≠ C}

/-- `M`: the principal block of `A = -(D_i·D_j)` on `D₀`. -/
def Mblock : Matrix (D0 R C) (D0 R C) ℚ := fun i j => R.A i.1 j.1

/-- `v`: the contact column `v_i = C · D_i` of `C` with `D₀`. -/
def vvec : D0 R C → ℚ := fun i => -R.A C i.1

/-- `q₀`: the canonical degrees `b_i - 2` on `D₀`. -/
def q0 : D0 R C → ℚ := fun i => R.q i.1

/-- `b = -C²`. -/
def bC : ℚ := R.w C

/-- `r`: the contacts `P · D_i` on `D₀`. -/
def rvec : D0 R C → ℚ := fun i => contactVector R P i.1

/-- `m = P · C`. -/
def mC : ℚ := contactVector R P C

/-- `λ₀`: the original discrepancy coefficients on `D₀`. -/
def lam0 : D0 R C → ℚ := fun i => R.lam i.1

/-- `μ = λ_C`: the original discrepancy coefficient of `C`. -/
def muC : ℚ := R.lam C

/-- Extension of a vector on `D₀` by the value `t` at `C`. -/
def ext (t : ℚ) (x : D0 R C → ℚ) : R.Vertices → ℚ :=
  fun i => if h : i = C then t else x ⟨i, h⟩

theorem ext_C (t : ℚ) (x : D0 R C → ℚ) : ext R C t x C = t := by
  simp [ext]

theorem ext_apply_of_ne (t : ℚ) (x : D0 R C → ℚ) {i : R.Vertices} (h : i ≠ C) :
    ext R C t x i = x ⟨i, h⟩ := dif_neg h

theorem ext_val (t : ℚ) (x : D0 R C → ℚ) (i : D0 R C) : ext R C t x i.1 = x i :=
  ext_apply_of_ne R C t x i.2

theorem A_symm (i j : R.Vertices) : R.A i j = R.A j i := by
  show -R.M i j = -R.M j i
  rw [M_symm R]

/-- Splitting a sum over the vertices at `C`. -/
theorem sum_split (f : R.Vertices → ℚ) : ∑ i, f i = f C + ∑ i : D0 R C, f i.1 := by
  rw [Fintype.sum_eq_add_sum_compl C f]
  congr 1
  exact Finset.sum_subtype ({C}ᶜ : Finset R.Vertices) (fun x => by simp) f

theorem dot_ext (t : ℚ) (x : D0 R C → ℚ) (z : R.Vertices → ℚ) :
    ext R C t x ⬝ᵥ z = t * z C + x ⬝ᵥ (fun i => z i.1) := by
  unfold dotProduct
  rw [sum_split R C, ext_C]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by rw [ext_val])

theorem mulVec_ext_C (t : ℚ) (x : D0 R C → ℚ) :
    (R.A *ᵥ ext R C t x) C = bC R C * t - vvec R C ⬝ᵥ x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_split R C, ext_C, R.A_diag]
  unfold bC vvec
  simp only [ext_val]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem mulVec_ext_val (t : ℚ) (x : D0 R C → ℚ) (i : D0 R C) :
    (R.A *ᵥ ext R C t x) i.1 = -(vvec R C i) * t + (Mblock R C *ᵥ x) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_split R C, ext_C]
  unfold vvec Mblock
  simp only [ext_val, neg_neg]
  rw [A_symm R i.1 C]

theorem lam_eq_ext : R.lam = ext R C (muC R C) (lam0 R C) := by
  funext i
  by_cases h : i = C
  · subst h
    rw [ext_C]
    rfl
  · rw [ext_apply_of_ne R C _ _ h]
    rfl

theorem q_eq_ext : R.q = ext R C (bC R C - 2) (q0 R C) := by
  funext i
  by_cases h : i = C
  · subst h
    rw [ext_C]
    rfl
  · rw [ext_apply_of_ne R C _ _ h]
    rfl

theorem contactVector_eq_ext : contactVector R P = ext R C (mC R C P) (rvec R C P) := by
  funext i
  by_cases h : i = C
  · subst h
    rw [ext_C]
    rfl
  · rw [ext_apply_of_ne R C _ _ h]
    rfl

/-! ### The block `M` is a positive definite Stieltjes matrix -/

theorem Mblock_symm (i j : D0 R C) : Mblock R C i j = Mblock R C j i := A_symm R i.1 j.1

theorem Mblock_isSymm : (Mblock R C).IsSymm := by
  ext i j
  exact Mblock_symm R C j i

theorem Mblock_isHermitian : (Mblock R C).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact Mblock_symm R C j i

theorem Mblock_offDiag_nonpos (i j : D0 R C) (hij : i ≠ j) : Mblock R C i j ≤ 0 :=
  R.A_offDiag_nonpos i.1 j.1 (fun h => hij (Subtype.ext h))

theorem Mblock_posDef : (Mblock R C).PosDef := by
  refine ⟨Mblock_isHermitian R C, ?_⟩
  intro x hx
  have hext : ext R C 0 x ≠ 0 := by
    intro h
    apply hx
    funext i
    have := congrFun h i.1
    rw [ext_val] at this
    exact this
  have hpos := R.A_posDef.2 (ext R C 0 x) hext
  simp only [star_trivial] at hpos ⊢
  rw [dot_ext, zero_mul, zero_add] at hpos
  convert hpos using 2
  funext i
  rw [mulVec_ext_val]
  ring

theorem Mblock_isUnit : IsUnit (Mblock R C).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (KltDP.LinearAlgebra.isUnit_of_posDef (Mblock_posDef R C))

theorem Mblock_mulVec_inv (x : D0 R C → ℚ) : Mblock R C *ᵥ ((Mblock R C)⁻¹ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Mblock_isUnit R C), Matrix.one_mulVec]

theorem Mblock_inv_mulVec (x : D0 R C → ℚ) : (Mblock R C)⁻¹ *ᵥ (Mblock R C *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Mblock_isUnit R C), Matrix.one_mulVec]

theorem Mblock_inv_nonneg (i j : D0 R C) : 0 ≤ (Mblock R C)⁻¹ i j :=
  KltDP.LinearAlgebra.stieltjes_inverse_nonnegative (Mblock_posDef R C)
    (Mblock_offDiag_nonpos R C) i j

theorem Mblock_inv_mulVec_nonneg {b : D0 R C → ℚ} (hb : ∀ i, 0 ≤ b i) (i : D0 R C) :
    0 ≤ ((Mblock R C)⁻¹ *ᵥ b) i :=
  KltDP.LinearAlgebra.stieltjes_inverse_mulVec_nonnegative (Mblock_posDef R C)
    (Mblock_offDiag_nonpos R C) hb i

/-- Symmetry of `M⁻¹`: `xᵀM⁻¹y = yᵀM⁻¹x`. -/
theorem dot_inv_comm (x y : D0 R C → ℚ) :
    x ⬝ᵥ ((Mblock R C)⁻¹ *ᵥ y) = y ⬝ᵥ ((Mblock R C)⁻¹ *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, Matrix.transpose_nonsing_inv,
    (Mblock_isSymm R C).eq, dotProduct_comm]

/-! ### Signs of the block data -/

theorem vvec_nonneg (i : D0 R C) : 0 ≤ vvec R C i := by
  unfold vvec
  have := R.A_offDiag_nonpos C i.1 (fun h => i.2 h.symm)
  linarith

theorem q0_nonneg (i : D0 R C) : 0 ≤ q0 R C i := by
  unfold q0 ResolutionDatum.q
  linarith [R.two_le_w i.1]

theorem rvec_nonneg (hP : ¬ IsExceptionalCurve R.π P) (i : D0 R C) : 0 ≤ rvec R C P i :=
  contactVector_nonneg R P hP i.1

theorem mC_nonneg (hP : ¬ IsExceptionalCurve R.π P) : 0 ≤ mC R C P :=
  contactVector_nonneg R P hP C

theorem muC_nonneg : 0 ≤ muC R C := R.lam_nonneg C

theorem lam0_nonneg (i : D0 R C) : 0 ≤ lam0 R C i := R.lam_nonneg i.1

theorem lam0_lt_one (i : D0 R C) : lam0 R C i < 1 := R.lam_lt_one i.1

/-- `r ≤ q₀` when all contacts with `D₀` are bounded (eq:replacement-simple-complement). -/
theorem rvec_le_q0 (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) (i : D0 R C) :
    rvec R C P i ≤ q0 R C i :=
  hbdd i.1 i.2

/-! ### The scalars (manuscript eq:replacement-scalars-1..3, lines 969–989) -/

/-- `M⁻¹ v`. -/
def wv : D0 R C → ℚ := (Mblock R C)⁻¹ *ᵥ vvec R C

/-- The Schur scalar `b - vᵀM⁻¹v`. -/
def schur : ℚ := bC R C - vvec R C ⬝ᵥ wv R C

/-- `g = (b - vᵀM⁻¹v)⁻¹`. -/
def gC : ℚ := (schur R C)⁻¹

/-- `θ = M⁻¹ q₀`. -/
def theta : D0 R C → ℚ := (Mblock R C)⁻¹ *ᵥ q0 R C

/-- `u = M⁻¹ r`. -/
def uvec : D0 R C → ℚ := (Mblock R C)⁻¹ *ᵥ rvec R C P

/-- `h = rᵀu`. -/
def hC : ℚ := rvec R C P ⬝ᵥ uvec R C P

/-- `η = rᵀθ`. -/
def eta : ℚ := rvec R C P ⬝ᵥ theta R C

/-- `α = vᵀu`. -/
def alpha : ℚ := vvec R C ⬝ᵥ uvec R C P

/-- `τ = m + α`. -/
def tau : ℚ := mC R C P + alpha R C P

/-- `c = (1-η)/(1-h)` (eq:replacement-new-data). -/
def cC : ℚ := (1 - eta R C P) / (1 - hC R C P)

/-- `λ₀† = θ - c u` (eq:replacement-new-data). -/
def lam0' : D0 R C → ℚ := theta R C - cC R C P • uvec R C P

theorem Mblock_mulVec_wv : Mblock R C *ᵥ wv R C = vvec R C := Mblock_mulVec_inv R C _

theorem Mblock_mulVec_theta : Mblock R C *ᵥ theta R C = q0 R C := Mblock_mulVec_inv R C _

theorem Mblock_mulVec_uvec : Mblock R C *ᵥ uvec R C P = rvec R C P := Mblock_mulVec_inv R C _

/-! ### The row equations `Aλ = q` in block form -/

/-- The `D₀`-rows: `M λ₀ = q₀ + μ v`. -/
theorem M_mulVec_lam0 : Mblock R C *ᵥ lam0 R C = q0 R C + muC R C • vvec R C := by
  funext i
  have h := congrFun R.A_mulVec_lam i.1
  rw [lam_eq_ext R C, mulVec_ext_val] at h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  unfold q0
  linarith

/-- `λ₀ = θ + μ M⁻¹v` (eq:old-restricted-discrepancy). -/
theorem lam0_eq : lam0 R C = theta R C + muC R C • wv R C := by
  have h := congrArg (fun y => (Mblock R C)⁻¹ *ᵥ y) (M_mulVec_lam0 R C)
  simp only at h
  rw [Mblock_inv_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul] at h
  exact h

/-- The `C`-row: `b μ - vᵀλ₀ = b - 2`. -/
theorem C_row : bC R C * muC R C - vvec R C ⬝ᵥ lam0 R C = bC R C - 2 := by
  have h := congrFun R.A_mulVec_lam C
  rw [lam_eq_ext R C, mulVec_ext_C] at h
  exact h

/-- `μ (b - vᵀM⁻¹v) = b - 2 + vᵀθ`. -/
theorem mu_mul_schur : muC R C * schur R C = bC R C - 2 + vvec R C ⬝ᵥ theta R C := by
  have h := C_row R C
  rw [lam0_eq R C, dotProduct_add, dotProduct_smul, smul_eq_mul] at h
  unfold schur
  linarith

/-- Positivity of the Schur scalar: `A` positive definite at `(1, M⁻¹v)`. -/
theorem schur_pos : 0 < schur R C := by
  have hne : ext R C 1 (wv R C) ≠ 0 := by
    intro h
    have := congrFun h C
    rw [ext_C] at this
    exact one_ne_zero this
  have hpos := R.A_posDef.2 (ext R C 1 (wv R C)) hne
  simp only [star_trivial] at hpos
  rw [dot_ext, mulVec_ext_C] at hpos
  have hrow : (fun i : D0 R C => (R.A *ᵥ ext R C 1 (wv R C)) i.1) =
      fun i => -(vvec R C i) * 1 + (Mblock R C *ᵥ wv R C) i := by
    funext i
    rw [mulVec_ext_val]
  rw [hrow, Mblock_mulVec_wv] at hpos
  have hzero : wv R C ⬝ᵥ (fun i => -(vvec R C i) * 1 + vvec R C i) = 0 := by
    unfold dotProduct
    apply Finset.sum_eq_zero
    intro i _
    ring
  rw [hzero] at hpos
  unfold schur
  linarith

theorem schur_ne_zero : schur R C ≠ 0 := ne_of_gt (schur_pos R C)

theorem gC_pos : 0 < gC R C := inv_pos.mpr (schur_pos R C)

theorem gC_mul_schur : gC R C * schur R C = 1 := inv_mul_cancel₀ (schur_ne_zero R C)

/-- `μ = g (b - 2 + vᵀθ)` (eq:replacement-scalars-2). -/
theorem muC_eq : muC R C = gC R C * (bC R C - 2 + vvec R C ⬝ᵥ theta R C) := by
  rw [← mu_mul_schur R C, mul_comm (muC R C), ← mul_assoc, gC_mul_schur, one_mul]

/-- `μ / g = b - 2 + vᵀθ`. -/
theorem muC_div_gC : muC R C / gC R C = bC R C - 2 + vvec R C ⬝ᵥ theta R C := by
  rw [← mu_mul_schur R C, div_eq_mul_inv]
  unfold gC
  rw [inv_inv]

/-! ### Signs and bounds of the scalars -/

theorem theta_nonneg (i : D0 R C) : 0 ≤ theta R C i :=
  Mblock_inv_mulVec_nonneg R C (q0_nonneg R C) i

theorem wv_nonneg (i : D0 R C) : 0 ≤ wv R C i :=
  Mblock_inv_mulVec_nonneg R C (vvec_nonneg R C) i

theorem uvec_nonneg (hP : ¬ IsExceptionalCurve R.π P) (i : D0 R C) : 0 ≤ uvec R C P i :=
  Mblock_inv_mulVec_nonneg R C (rvec_nonneg R C P hP) i

theorem alpha_nonneg (hP : ¬ IsExceptionalCurve R.π P) : 0 ≤ alpha R C P :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (vvec_nonneg R C i) (uvec_nonneg R C P hP i))

/-- `u ≤ θ` coordinatewise (positivity of `M⁻¹` and `r ≤ q₀`). -/
theorem uvec_le_theta (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) (i : D0 R C) :
    uvec R C P i ≤ theta R C i :=
  KltDP.LinearAlgebra.mulVec_mono_of_entrywise_nonnegative (Mblock_inv_nonneg R C)
    (rvec_le_q0 R C P hbdd) i

/-- `θ ≤ λ₀` coordinatewise. -/
theorem theta_le_lam0 (i : D0 R C) : theta R C i ≤ lam0 R C i := by
  rw [lam0_eq R C]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [muC_nonneg R C, wv_nonneg R C i]

theorem hC_nonneg (hP : ¬ IsExceptionalCurve R.π P) : 0 ≤ hC R C P :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (rvec_nonneg R C P hP i) (uvec_nonneg R C P hP i))

theorem hC_le_eta (hP : ¬ IsExceptionalCurve R.π P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) : hC R C P ≤ eta R C P :=
  KltDP.LinearAlgebra.dotProduct_mono_right_of_nonnegative (rvec_nonneg R C P hP)
    (uvec_le_theta R C P hbdd)

theorem eta_le_rvec_lam0 (hP : ¬ IsExceptionalCurve R.π P) :
    eta R C P ≤ rvec R C P ⬝ᵥ lam0 R C :=
  KltDP.LinearAlgebra.dotProduct_mono_right_of_nonnegative (rvec_nonneg R C P hP)
    (theta_le_lam0 R C)

/-- `pᵀλ = m μ + rᵀλ₀`. -/
theorem contact_dot_lam :
    contactVector R P ⬝ᵥ R.lam = mC R C P * muC R C + rvec R C P ⬝ᵥ lam0 R C := by
  rw [contactVector_eq_ext R C P, dot_ext]
  rfl

theorem rvec_lam0_lt_one (hP : R.IsExteriorMinusOne P) : rvec R C P ⬝ᵥ lam0 R C < 1 := by
  have h := rankOneProjection_charge_lt_one R P hP
  rw [contact_dot_lam R C P] at h
  have := mul_nonneg (mC_nonneg R C P hP.2) (muC_nonneg R C)
  linarith

theorem eta_lt_one (hP : R.IsExteriorMinusOne P) : eta R C P < 1 :=
  lt_of_le_of_lt (eta_le_rvec_lam0 R C P hP.2) (rvec_lam0_lt_one R C P hP)

theorem hC_lt_one (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) : hC R C P < 1 :=
  lt_of_le_of_lt (hC_le_eta R C P hP.2 hbdd) (eta_lt_one R C P hP)

theorem cC_pos (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) : 0 < cC R C P :=
  KltDP.LinearAlgebra.replacement_coefficient_pos (hC_lt_one R C P hP hbdd) (eta_lt_one R C P hP)

/-- `-c < 1` (eq:replacement-coefficient-bounds). -/
theorem neg_cC_lt_one (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) : -cC R C P < 1 :=
  KltDP.LinearAlgebra.neg_replacement_coefficient_lt_one (hC_lt_one R C P hP hbdd)
    (eta_lt_one R C P hP)

/-- `c ≤ 1`, since `h ≤ η`. -/
theorem cC_le_one (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) : cC R C P ≤ 1 := by
  unfold cC
  rw [div_le_one (sub_pos.mpr (hC_lt_one R C P hP hbdd))]
  linarith [hC_le_eta R C P hP.2 hbdd]

/-- `c (1 - h) = 1 - η`. -/
theorem cC_mul_one_sub_hC (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) :
    cC R C P * (1 - hC R C P) = 1 - eta R C P := by
  unfold cC
  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr (hC_lt_one R C P hP hbdd)))

/-- `0 ≤ λ₀†` (eq:replacement-coefficient-bounds). -/
theorem lam0'_nonneg (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) (i : D0 R C) :
    0 ≤ lam0' R C P i := by
  unfold lam0'
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := uvec_le_theta R C P hbdd i
  have h2 := uvec_nonneg R C P hP.2 i
  have h3 := cC_le_one R C P hP hbdd
  nlinarith

/-- `λ₀† ≤ θ`. -/
theorem lam0'_le_theta (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) (i : D0 R C) :
    lam0' R C P i ≤ theta R C i := by
  unfold lam0'
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [uvec_nonneg R C P hP.2 i, cC_pos R C P hP hbdd]

/-- `λ₀† ≤ λ₀` (eq:replacement-coefficient-bounds). -/
theorem lam0'_le_lam0 (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) (i : D0 R C) :
    lam0' R C P i ≤ lam0 R C i :=
  le_trans (lam0'_le_theta R C P hP hbdd i) (theta_le_lam0 R C i)

theorem lam0'_lt_one (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) (i : D0 R C) :
    lam0' R C P i < 1 :=
  lt_of_le_of_lt (lam0'_le_lam0 R C P hP hbdd i) (lam0_lt_one R C i)

/-- Rank-one identity (eq:replacement-new-data): `(M - r rᵀ) λ₀† = q₀ - r`. -/
theorem rankOne_mulVec_lam0' (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) :
    (Mblock R C - vecMulVec (rvec R C P) (rvec R C P)) *ᵥ lam0' R C P = q0 R C - rvec R C P := by
  funext i
  have hM : (Mblock R C *ᵥ lam0' R C P) i = q0 R C i - cC R C P * rvec R C P i := by
    unfold lam0'
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Mblock_mulVec_theta, Mblock_mulVec_uvec]
    simp
  have hr : (vecMulVec (rvec R C P) (rvec R C P) *ᵥ lam0' R C P) i =
      rvec R C P i * (rvec R C P ⬝ᵥ lam0' R C P) := by
    simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]
  have hdot : rvec R C P ⬝ᵥ lam0' R C P = eta R C P - cC R C P * hC R C P := by
    unfold lam0' eta hC
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [Matrix.sub_mulVec, Pi.sub_apply, hM, hr, hdot, Pi.sub_apply]
  have hc := cC_mul_one_sub_hC R C P hP hbdd
  linear_combination (-(rvec R C P i)) * hc

/-! ### The energy identities (eq:replacement-old-energy, line 1062) -/

/-- `rᵀM⁻¹v = vᵀM⁻¹r = α`. -/
theorem rvec_dot_wv : rvec R C P ⬝ᵥ wv R C = alpha R C P := by
  unfold wv alpha uvec
  exact dot_inv_comm R C _ _

/-- `pᵀλ = η + τ μ`. -/
theorem contact_dot_lam_eq : contactVector R P ⬝ᵥ R.lam = eta R C P + tau R C P * muC R C := by
  rw [contact_dot_lam R C P, lam0_eq R C, dotProduct_add, dotProduct_smul, smul_eq_mul,
    rvec_dot_wv]
  unfold tau eta
  ring

/-- `ℓ = L·P = 1 - η - τ μ` (eq:replacement-scalars-3). -/
theorem Ldeg_eq (hP : R.IsExteriorMinusOne P) :
    R.Ldeg P = 1 - eta R C P - tau R C P * muC R C := by
  have h := rankOneProjection_charge R P hP
  rw [contact_dot_lam_eq R C P] at h
  linarith

/-- The solution `z = (gτ, u + gτ M⁻¹v)` of `A z = p`. -/
def zvec : R.Vertices → ℚ :=
  ext R C (gC R C * tau R C P) (uvec R C P + (gC R C * tau R C P) • wv R C)

theorem A_mulVec_zvec : R.A *ᵥ zvec R C P = contactVector R P := by
  rw [contactVector_eq_ext R C P]
  funext i
  by_cases h : i = C
  · rw [h]
    unfold zvec
    rw [mulVec_ext_C, ext_C, dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hg := gC_mul_schur R C
    unfold schur at hg
    unfold tau alpha
    linear_combination (mC R C P + vvec R C ⬝ᵥ uvec R C P) * hg
  · have hi : i = (⟨i, h⟩ : D0 R C).1 := rfl
    rw [hi]
    unfold zvec
    rw [mulVec_ext_val, ext_val, Matrix.mulVec_add, Matrix.mulVec_smul, Mblock_mulVec_uvec,
      Mblock_mulVec_wv]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem A_inv_mulVec_contact : R.A⁻¹ *ᵥ contactVector R P = zvec R C P := by
  rw [← A_mulVec_zvec R C P, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (A_det_isUnit R),
    Matrix.one_mulVec]

/-- `pᵀA⁻¹p = h + g τ²` (eq:replacement-old-energy). -/
theorem energy : contactVector R P ⬝ᵥ (R.A⁻¹ *ᵥ contactVector R P) =
    hC R C P + gC R C * tau R C P ^ 2 := by
  rw [A_inv_mulVec_contact R C P, contactVector_eq_ext R C P]
  unfold zvec
  rw [dot_ext]
  have hrest : (fun i : D0 R C =>
      ext R C (gC R C * tau R C P) (uvec R C P + (gC R C * tau R C P) • wv R C) i.1) =
      uvec R C P + (gC R C * tau R C P) • wv R C := by
    funext i
    rw [ext_val]
  rw [hrest, ext_C, dotProduct_add, dotProduct_smul, smul_eq_mul, rvec_dot_wv]
  unfold hC tau
  ring

/-- `1 < h + g τ²` (from Lemma 2.8). -/
theorem one_lt_energy (p : ℕ) [CharP k p] (hp : 0 < p) (hP : R.IsExteriorMinusOne P) :
    1 < hC R C P + gC R C * tau R C P ^ 2 := by
  rw [← energy R C P]
  exact rankOneProjection_green_gt_one R p hp P hP

/-- `τ > 0`: `m = P·C > 0` at the excess contact `C` and `α ≥ 0`. -/
theorem tau_pos (hP : R.IsExteriorMinusOne P) (hexC : IsExcessContact R P C) : 0 < tau R C P := by
  have hm : 0 < mC R C P := contact_pos_of_excess R P C hexC
  have ha := alpha_nonneg R C P hP.2
  unfold tau
  linarith

theorem Ldeg_pos' (hP : R.IsExteriorMinusOne P) : 0 < 1 - eta R C P - tau R C P * muC R C := by
  rw [← Ldeg_eq R C P hP]
  exact Ldeg_pos R P hP.2

/-- eq:replacement-square-gain, scalar form: `(1-η)²/(1-h) - μ²/g > 0`. -/
theorem square_gain_pos (p : ℕ) [CharP k p] (hp : 0 < p) (hP : R.IsExteriorMinusOne P)
    (hexC : IsExcessContact R P C)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) :
    0 < (1 - eta R C P) ^ 2 / (1 - hC R C P) - muC R C ^ 2 / gC R C :=
  KltDP.LinearAlgebra.replacement_square_gain_pos (gC_pos R C) (hC_lt_one R C P hP hbdd)
    (tau_pos R C P hP hexC) (muC_nonneg R C) (Ldeg_pos' R C P hP) (one_lt_energy R C P p hp hP)

/-- eq:replacement-deleted-degree, scalar form: `τ c - μ/g > 0`. -/
theorem deleted_degree_pos (p : ℕ) [CharP k p] (hp : 0 < p) (hP : R.IsExteriorMinusOne P)
    (hexC : IsExcessContact R P C)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) :
    0 < tau R C P * cC R C P - muC R C / gC R C :=
  KltDP.LinearAlgebra.replacement_deleted_degree_pos (gC_pos R C) (hC_lt_one R C P hP hbdd)
    (tau_pos R C P hP hexC) (muC_nonneg R C) (Ldeg_pos' R C P hP) (one_lt_energy R C P p hp hP)

/-! ### Sums over `D₀ ⊕ Unit` -/

theorem mulVec_sum_apply (N : Matrix (D0 R C ⊕ Unit) (D0 R C ⊕ Unit) ℚ) (x : D0 R C ⊕ Unit → ℚ)
    (a : D0 R C ⊕ Unit) :
    (N *ᵥ x) a = ∑ j : D0 R C, N a (Sum.inl j) * x (Sum.inl j) + N a (Sum.inr ()) * x (Sum.inr ()) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sum_type, Fintype.sum_unique (fun u : Unit => N a (Sum.inr u) * x (Sum.inr u))]

theorem dot_sum (x y : D0 R C ⊕ Unit → ℚ) :
    x ⬝ᵥ y = ∑ j : D0 R C, x (Sum.inl j) * y (Sum.inl j) + x (Sum.inr ()) * y (Sum.inr ()) := by
  unfold dotProduct
  rw [Fintype.sum_sum_type, Fintype.sum_unique (fun u : Unit => x (Sum.inr u) * y (Sum.inr u))]

/-! ### The retained family `G† = P + D₀` and its null equations -/

/-- The retained family, indexed by `D₀ ⊕ Unit` (`P` last). -/
def famG : D0 R C ⊕ Unit → R.S.PrimeCurve := Sum.elim (fun i => i.1.1) (fun _ => P)

/-- The new coefficient vector `λ† = (λ₀†, -c)` (the coefficient of `P` is `-c`, manuscript
line 1010). -/
def lamG : D0 R C ⊕ Unit → ℚ := Sum.elim (lam0' R C P) (fun _ => -cC R C P)

@[simp] theorem famG_inl (i : D0 R C) : famG R C P (Sum.inl i) = i.1.1 := rfl
@[simp] theorem famG_inr (u : Unit) : famG R C P (Sum.inr u) = P := rfl
@[simp] theorem lamG_inl (i : D0 R C) : lamG R C P (Sum.inl i) = lam0' R C P i := rfl
@[simp] theorem lamG_inr (u : Unit) : lamG R C P (Sum.inr u) = -cC R C P := rfl

theorem famG_injective (hP : ¬ IsExceptionalCurve R.π P) : Function.Injective (famG R C P) := by
  rintro (i | u) (j | w) h
  · simp only [famG_inl] at h
    exact congrArg Sum.inl (Subtype.ext (Subtype.ext h))
  · simp only [famG_inl, famG_inr] at h
    exact absurd (h ▸ i.1.property) hP
  · simp only [famG_inl, famG_inr] at h
    exact absurd (h.symm ▸ j.1.property) hP
  · rfl

/-- `P·D_i = D_i·P` as intersection pairings. -/
theorem pairing_val_P (i : D0 R C) :
    (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1.1)
      (R.S.primeCurveCartier R.hreg P) : ℚ) = rvec R C P i := by
  rw [R.S.intersectionPairing_primeCurve R.hreg]
  rfl

theorem pairing_P_val (i : D0 R C) :
    (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg P)
      (R.S.primeCurveCartier R.hreg i.1.1) : ℚ) = rvec R C P i := by
  rw [R.S.intersectionPairing_symm R.hreg]
  exact pairing_val_P R C P i

theorem pairing_P_P (hP : IsMinusOneCurve R.hreg P) :
    (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg P)
      (R.S.primeCurveCartier R.hreg P) : ℚ) = -1 := by
  rw [R.S.intersectionPairing_primeCurve R.hreg]
  have h : P.intersectionNumber (R.S.primeCurveCartier R.hreg P) = -1 := hP.selfIntersection
  rw [h]
  norm_num

theorem negIntersectionMatrix_famG_inl_inl (i j : D0 R C) :
    negIntersectionMatrix R.S R.hreg (famG R C P) (Sum.inl i) (Sum.inl j) = Mblock R C i j := rfl

theorem negIntersectionMatrix_famG_inl_inr (i : D0 R C) (u : Unit) :
    negIntersectionMatrix R.S R.hreg (famG R C P) (Sum.inl i) (Sum.inr u) = -rvec R C P i := by
  unfold negIntersectionMatrix NullCurveIntersectionMatrix.intersectionMatrix
  simp only [Matrix.neg_apply, famG_inl, famG_inr]
  rw [pairing_val_P]

theorem negIntersectionMatrix_famG_inr_inl (u : Unit) (j : D0 R C) :
    negIntersectionMatrix R.S R.hreg (famG R C P) (Sum.inr u) (Sum.inl j) = -rvec R C P j := by
  unfold negIntersectionMatrix NullCurveIntersectionMatrix.intersectionMatrix
  simp only [Matrix.neg_apply, famG_inl, famG_inr]
  rw [pairing_P_val]

theorem negIntersectionMatrix_famG_inr_inr (hP : IsMinusOneCurve R.hreg P) (u w : Unit) :
    negIntersectionMatrix R.S R.hreg (famG R C P) (Sum.inr u) (Sum.inr w) = 1 := by
  unfold negIntersectionMatrix NullCurveIntersectionMatrix.intersectionMatrix
  simp only [Matrix.neg_apply, famG_inr]
  rw [pairing_P_P R P hP]
  norm_num

theorem canonicalDegreeVector_famG_inl (i : D0 R C) :
    canonicalDegreeVector R.S (famG R C P) R.KS (Sum.inl i) = q0 R C i := by
  unfold canonicalDegreeVector q0
  simp only [famG_inl]
  exact R.Kdeg_exceptional i.1

theorem canonicalDegreeVector_famG_inr (hP : IsMinusOneCurve R.hreg P) (u : Unit) :
    canonicalDegreeVector R.S (famG R C P) R.KS (Sum.inr u) = -1 := by
  unfold canonicalDegreeVector
  simp only [famG_inr]
  have h := Kdeg_eq_neg_one_of_isMinusOne R P hP
  unfold ResolutionDatum.Kdeg at h
  rw [h]
  norm_num

/-- The null equations `A† (λ₀†, -c) = q†` (manuscript lines 1054–1060). -/
theorem negIntersectionMatrix_famG_mulVec_lamG (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) :
    negIntersectionMatrix R.S R.hreg (famG R C P) *ᵥ lamG R C P =
      canonicalDegreeVector R.S (famG R C P) R.KS := by
  have hM : (Mblock R C *ᵥ lam0' R C P) = q0 R C - cC R C P • rvec R C P := by
    unfold lam0'
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Mblock_mulVec_theta, Mblock_mulVec_uvec]
  have hdot : rvec R C P ⬝ᵥ lam0' R C P = eta R C P - cC R C P * hC R C P := by
    unfold lam0' eta hC
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hc := cC_mul_one_sub_hC R C P hP hbdd
  funext x
  rcases x with i | u
  · rw [canonicalDegreeVector_famG_inl, mulVec_sum_apply]
    simp only [negIntersectionMatrix_famG_inl_inl, negIntersectionMatrix_famG_inl_inr,
      lamG_inl, lamG_inr]
    have hMi := congrFun hM i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hMi
    linear_combination hMi
  · rw [canonicalDegreeVector_famG_inr R C P hP.1, mulVec_sum_apply]
    simp only [negIntersectionMatrix_famG_inr_inl, negIntersectionMatrix_famG_inr_inr R C P hP.1,
      lamG_inl, lamG_inr]
    have hsum : ∑ j : D0 R C, -rvec R C P j * lam0' R C P j =
        -(rvec R C P ⬝ᵥ lam0' R C P) := by
      unfold dotProduct
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsum, hdot]
    linear_combination -hc

/-! ### The class `L† = -(K_S + Σ λ†_j G†_j)` and its square and degree on `C` -/

/-- `L† ∈ N¹(S)_ℚ` (eq:replacement-anticanonical). -/
def Lnum' : R.S.NumericalClassGroup := adjustedClass R.S R.hreg (famG R C P) R.KS (lamG R C P)

/-- `(L†)²`. -/
def Lsq' : ℚ := R.S.numericalIntersectionBilinForm R.hreg (Lnum' R C P) (Lnum' R C P)

theorem lamG_dot_canonicalDegreeVector (hP : IsMinusOneCurve R.hreg P) :
    lamG R C P ⬝ᵥ canonicalDegreeVector R.S (famG R C P) R.KS =
      lam0' R C P ⬝ᵥ q0 R C + cC R C P := by
  rw [dot_sum]
  simp only [lamG_inl, lamG_inr, canonicalDegreeVector_famG_inl,
    canonicalDegreeVector_famG_inr R C P hP]
  unfold dotProduct
  ring

/-- `(L†)² = K_S² + λ₀†ᵀq₀ + c` (Lemma 2.5). -/
theorem Lsq'_eq (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) :
    Lsq' R C P = R.Ksq + (lam0' R C P ⬝ᵥ q0 R C + cC R C P) := by
  unfold Lsq' Lnum'
  rw [square_formula R.S R.hreg (famG R C P) R.KS (lamG R C P)
    (negIntersectionMatrix_famG_mulVec_lamG R C P hP hbdd), lamG_dot_canonicalDegreeVector R C P hP.1]
  rfl

/-- `L² = K_S² + (b-2) μ + q₀ᵀλ₀`. -/
theorem Lsq_eq_block : R.Lsq = R.Ksq + ((bC R C - 2) * muC R C + q0 R C ⬝ᵥ lam0 R C) := by
  rw [R.Lsq_eq_Ksq_add_dot, q_eq_ext R C, dot_ext]
  rfl

/-- `uᵀq₀ = η` and `vᵀλ₀-type` symmetric pairings. -/
theorem uvec_dot_q0 : uvec R C P ⬝ᵥ q0 R C = eta R C P := by
  unfold uvec eta theta
  rw [dotProduct_comm]
  exact dot_inv_comm R C _ _

theorem q0_dot_wv : q0 R C ⬝ᵥ wv R C = vvec R C ⬝ᵥ theta R C := by
  unfold wv theta
  exact dot_inv_comm R C _ _

/-- eq:replacement-square-gain: `(L†)² - L² = (1-η)²/(1-h) - μ²/g`. -/
theorem Lsq'_sub_Lsq (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) :
    Lsq' R C P - R.Lsq = (1 - eta R C P) ^ 2 / (1 - hC R C P) - muC R C ^ 2 / gC R C := by
  rw [Lsq'_eq R C P hP hbdd, Lsq_eq_block R C]
  have h1 : lam0' R C P ⬝ᵥ q0 R C = theta R C ⬝ᵥ q0 R C - cC R C P * eta R C P := by
    unfold lam0'
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, uvec_dot_q0]
  have h2 : q0 R C ⬝ᵥ lam0 R C = theta R C ⬝ᵥ q0 R C + muC R C * (vvec R C ⬝ᵥ theta R C) := by
    rw [lam0_eq R C, dotProduct_add, dotProduct_smul, smul_eq_mul, q0_dot_wv, dotProduct_comm]
  have h3 := muC_div_gC R C
  have hc := cC_mul_one_sub_hC R C P hP hbdd
  have hh : (1 - hC R C P) ≠ 0 := ne_of_gt (sub_pos.mpr (hC_lt_one R C P hP hbdd))
  have hg : gC R C ≠ 0 := ne_of_gt (gC_pos R C)
  have hsq : (1 - eta R C P) ^ 2 / (1 - hC R C P) = cC R C P * (1 - eta R C P) := by
    rw [← hc]
    unfold cC
    field_simp
    ring
  have hmu : muC R C ^ 2 / gC R C = muC R C * (bC R C - 2 + vvec R C ⬝ᵥ theta R C) := by
    rw [← h3, pow_two, mul_div_assoc]
  rw [h1, h2, hsq, hmu]
  ring

/-- eq:replacement-square-gain: `(L†)² > L²`. -/
theorem Lsq_lt_Lsq' (p : ℕ) [CharP k p] (hp : 0 < p) (hP : R.IsExteriorMinusOne P)
    (hexC : IsExcessContact R P C)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) : R.Lsq < Lsq' R C P := by
  have h := square_gain_pos R C P p hp hP hexC hbdd
  rw [← Lsq'_sub_Lsq R C P hP hbdd] at h
  linarith

theorem Lsq'_pos (p : ℕ) [CharP k p] (hp : 0 < p) (hP : R.IsExteriorMinusOne P)
    (hexC : IsExcessContact R P C)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) : 0 < Lsq' R C P :=
  lt_trans R.Lsq_pos (Lsq_lt_Lsq' R C P p hp hP hexC hbdd)

/-- `C · D_i = v_i` as intersection numbers. -/
theorem C_intersectionNumber_val (i : D0 R C) :
    (C.1.intersectionNumber (R.S.primeCurveCartier R.hreg i.1.1) : ℚ) = vvec R C i := by
  unfold vvec
  have h : R.A C i.1 = -(R.M C i.1) := rfl
  rw [h, neg_neg]
  unfold ResolutionDatum.M NullCurveIntersectionMatrix.intersectionMatrix
  rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber]

/-- `C · P = m` as intersection numbers. -/
theorem C_intersectionNumber_P :
    (C.1.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = mC R C P := by
  unfold mC contactVector ResolutionDatum.contact
  rw [← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber,
    R.S.intersectionPairing_symm R.hreg,
    PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber]

/-- eq:replacement-deleted-degree: `L†·C = τ c - μ/g`. -/
theorem degree_C (hP : R.IsExteriorMinusOne P) :
    R.S.numericalRestrictionDegree C.1 (Lnum' R C P) = tau R C P * cC R C P - muC R C / gC R C := by
  unfold Lnum'
  rw [degree_formula R.S R.hreg (famG R C P) R.KS (lamG R C P) C.1]
  have hK : (C.1.intersectionNumber R.KS : ℚ) = bC R C - 2 := R.Kdeg_exceptional C
  rw [hK, dot_sum]
  simp only [famG_inl, famG_inr, lamG_inl, lamG_inr, C_intersectionNumber_val]
  rw [C_intersectionNumber_P R C P]
  have hv : ∑ i : D0 R C, vvec R C i * lam0' R C P i =
      vvec R C ⬝ᵥ theta R C - cC R C P * alpha R C P := by
    unfold lam0' alpha
    rw [← dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [hv, muC_div_gC R C]
  unfold tau
  ring

/-- eq:replacement-deleted-degree: `L†·C > 0`. -/
theorem degree_C_pos (p : ℕ) [CharP k p] (hp : 0 < p) (hP : R.IsExteriorMinusOne P)
    (hexC : IsExcessContact R P C)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) :
    0 < R.S.numericalRestrictionDegree C.1 (Lnum' R C P) := by
  rw [degree_C R C P hP]
  exact deleted_degree_pos R C P p hp hP hexC hbdd


/-! ### (iv) `L†` is nef with null locus exactly `G† = P + D₀` -/

/-- Splitting a sum over the vertices at `C`, for any additive commutative monoid. -/
theorem sum_split' {M : Type*} [AddCommMonoid M] (f : R.Vertices → M) :
    ∑ i, f i = f C + ∑ i : D0 R C, f i.1 := by
  rw [Fintype.sum_eq_add_sum_compl C f]
  congr 1
  exact Finset.sum_subtype ({C}ᶜ : Finset R.Vertices) (fun x => by simp) f

/-- eq:replacement-effective-difference: `L† = L + μ C + Σ_{D₀} (λ_i - λ†_i) D_i + c P` in `N¹(S)_ℚ`. -/
theorem Lnum'_eq :
    Lnum' R C P = R.Lnum + muC R C • DisjointNegativeCurvesRank.curveClass R.S R.hreg C.1 +
      ∑ i : D0 R C, (lam0 R C i - lam0' R C P i) •
        DisjointNegativeCurvesRank.curveClass R.S R.hreg i.1.1 +
      cC R C P • DisjointNegativeCurvesRank.curveClass R.S R.hreg P := by
  rw [R.Lnum_eq]
  unfold Lnum' adjustedClass curveCombination
  rw [Fintype.sum_sum_type, Fintype.sum_unique (fun u : Unit =>
    lamG R C P (Sum.inr u) • DisjointNegativeCurvesRank.curveClass R.S R.hreg (famG R C P (Sum.inr u)))]
  rw [sum_split' R C (fun i : R.Vertices =>
    R.lam i • DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val)]
  simp only [famG_inl, famG_inr, lamG_inl, lamG_inr, sub_smul, Finset.sum_sub_distrib, neg_smul]
  unfold muC lam0 ResolutionDatum.Knum
  abel

/-- `Q · E ≥ 0` for distinct prime curves. -/
theorem intersectionNumber_nonneg_of_ne (Q E : R.S.PrimeCurve) (h : Q ≠ E) :
    0 ≤ (Q.intersectionNumber (R.S.primeCurveCartier R.hreg E) : ℚ) := by
  have := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg R.S R.hreg Q E h
  rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber] at this
  exact_mod_cast this

/-- The degree of `L†` on a prime curve `Q`, from eq:replacement-effective-difference. -/
theorem degree_Lnum' (Q : R.S.PrimeCurve) :
    R.S.numericalRestrictionDegree Q (Lnum' R C P) =
      R.Ldeg Q + muC R C * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C.1) : ℚ) +
      ∑ i : D0 R C, (lam0 R C i - lam0' R C P i) *
        (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1.1) : ℚ) +
      cC R C P * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) := by
  rw [Lnum'_eq]
  simp only [map_add, map_sum, map_smul, smul_eq_mul, R.numericalRestrictionDegree_Lnum,
    numericalRestrictionDegree_curveClass R.S R.hreg]

/-- `L† · Q > 0` for every exterior prime curve `Q ≠ P` (manuscript lines 1081–1083). -/
theorem degree_Lnum'_pos_of_exterior (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i)
    (Q : R.S.PrimeCurve) (hQ : ¬ IsExceptionalCurve R.π Q) (hQP : Q ≠ P) :
    0 < R.S.numericalRestrictionDegree Q (Lnum' R C P) := by
  rw [degree_Lnum']
  have h1 := Ldeg_pos R Q hQ
  have h2 : 0 ≤ muC R C * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C.1) : ℚ) :=
    mul_nonneg (muC_nonneg R C)
      (intersectionNumber_nonneg_of_ne R Q C.1 (fun h => hQ (by rw [h]; exact C.2)))
  have h3 : 0 ≤ ∑ i : D0 R C, (lam0 R C i - lam0' R C P i) *
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1.1) : ℚ) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sub_nonneg.2 (lam0'_le_lam0 R C P hP hbdd i))
      (intersectionNumber_nonneg_of_ne R Q i.1.1 (fun h => hQ (by rw [h]; exact i.1.2))))
  have h4 : 0 ≤ cC R C P * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) :=
    mul_nonneg (cC_pos R C P hP hbdd).le (intersectionNumber_nonneg_of_ne R Q P hQP)
  linarith

/-- `L† · G†_j = 0` for every member of the retained family (the null equations). -/
theorem degree_Lnum'_famG (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) (j : D0 R C ⊕ Unit) :
    R.S.numericalRestrictionDegree (famG R C P j) (Lnum' R C P) = 0 := by
  unfold Lnum'
  rw [degree_formula R.S R.hreg (famG R C P) R.KS (lamG R C P) (famG R C P j)]
  have hnull := congrFun (negIntersectionMatrix_famG_mulVec_lamG R C P hP hbdd) j
  have hrow : (fun l => ((famG R C P j).intersectionNumber
      (R.S.primeCurveCartier R.hreg (famG R C P l)) : ℚ)) ⬝ᵥ lamG R C P =
      -(negIntersectionMatrix R.S R.hreg (famG R C P) *ᵥ lamG R C P) j := by
    simp only [Matrix.mulVec, dotProduct, negIntersectionMatrix,
      NullCurveIntersectionMatrix.intersectionMatrix, Matrix.neg_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber]
    ring
  rw [hrow, hnull]
  unfold canonicalDegreeVector
  ring

/-- `L†` is nef: nonnegative degree on every prime curve. -/
theorem degree_Lnum'_nonneg (p : ℕ) [CharP k p] (hp : 0 < p) (hP : R.IsExteriorMinusOne P)
    (hexC : IsExcessContact R P C)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) (Q : R.S.PrimeCurve) :
    0 ≤ R.S.numericalRestrictionDegree Q (Lnum' R C P) := by
  by_cases hQ : IsExceptionalCurve R.π Q
  · by_cases hQC : Q = C.1
    · rw [hQC]
      exact (degree_C_pos R C P p hp hP hexC hbdd).le
    · have h := degree_Lnum'_famG R C P hP hbdd
        (Sum.inl ⟨⟨Q, hQ⟩, fun h => hQC (congrArg Subtype.val h)⟩)
      exact le_of_eq h.symm
  · by_cases hQP : Q = P
    · rw [hQP]
      exact le_of_eq (degree_Lnum'_famG R C P hP hbdd (Sum.inr ())).symm
    · exact (degree_Lnum'_pos_of_exterior R C P hP hbdd Q hQ hQP).le

/-- The null locus of `L†` is exactly `G† = P + D₀` (manuscript lines 1083–1084). -/
theorem degree_Lnum'_eq_zero_iff (p : ℕ) [CharP k p] (hp : 0 < p) (hP : R.IsExteriorMinusOne P)
    (hexC : IsExcessContact R P C)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) (Q : R.S.PrimeCurve) :
    R.S.numericalRestrictionDegree Q (Lnum' R C P) = 0 ↔ ∃ j, Q = famG R C P j := by
  constructor
  · intro h0
    by_cases hQ : IsExceptionalCurve R.π Q
    · by_cases hQC : Q = C.1
      · exfalso
        rw [hQC] at h0
        exact (degree_C_pos R C P p hp hP hexC hbdd).ne' h0
      · exact ⟨Sum.inl ⟨⟨Q, hQ⟩, fun h => hQC (congrArg Subtype.val h)⟩, rfl⟩
    · by_cases hQP : Q = P
      · exact ⟨Sum.inr (), hQP⟩
      · exfalso
        exact (degree_Lnum'_pos_of_exterior R C P hP hbdd Q hQ hQP).ne' h0
  · rintro ⟨j, rfl⟩
    exact degree_Lnum'_famG R C P hP hbdd j

/-! ### (v) A Cartier multiple of `L†` and the contraction (Theorem 2.6) -/

/-- The rational Weil divisor `K_S + Σ_j λ†_j G†_j = -L†`. -/
def Dweil : R.S.RationalWeilDivisor :=
  R.S.rationalCartierToWeilHom R.KS + ∑ j, Finsupp.single (famG R C P j) (lamG R C P j)

/-- Clearing denominators: an actual Cartier divisor `Hm` with `Hm = -n (K_S + Σ λ†_j G†_j)`. -/
theorem exists_cartier_multiple : ∃ (n : ℕ) (Hm : CartierDivisor R.S.toScheme), 0 < n ∧
    R.S.rationalCartierToWeilHom Hm = -((n : ℚ) • Dweil R C P) := by
  obtain ⟨n, hn, A, hA⟩ := R.S.exists_positive_integral_multiple (Dweil R C P)
  refine ⟨n, (R.S.regularCartierWeilEquiv R.hreg).symm (-A), hn, ?_⟩
  have h1 : R.S.rationalCartierToWeilHom ((R.S.regularCartierWeilEquiv R.hreg).symm (-A)) =
      rationalizeWeilDivisor R.S (-A) := by
    change rationalizeWeilDivisor R.S (R.S.cartierToWeilHom _) = _
    rw [← R.S.regularCartierWeilEquiv_apply R.hreg, AddEquiv.apply_symm_apply]
  rw [h1, map_neg, hA, Nat.cast_smul_eq_nsmul]

/-- The numerical class of `K_S + Σ λ†_j G†_j` is `-L†`. -/
theorem rationalWeilNumericalMap_Dweil :
    R.S.rationalWeilNumericalMap R.hreg (Dweil R C P) = -(Lnum' R C P) := by
  unfold Dweil Lnum' adjustedClass curveCombination
  rw [map_add, map_sum, R.rationalWeilNumericalMap_rationalCartier, neg_neg]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finsupp.smul_single_one, map_smul, R.rationalWeilNumericalMap_single]

theorem cartierClass_Hm {n : ℕ} {Hm : CartierDivisor R.S.toScheme}
    (hHm : R.S.rationalCartierToWeilHom Hm = -((n : ℚ) • Dweil R C P)) :
    NefNullCurveNegativeSquare.cartierClass R.S Hm = (n : ℚ) • Lnum' R C P := by
  rw [← R.rationalWeilNumericalMap_rationalCartier, hHm, map_neg, map_smul,
    rationalWeilNumericalMap_Dweil, smul_neg, neg_neg]

theorem intersectionNumber_Hm {n : ℕ} {Hm : CartierDivisor R.S.toScheme}
    (hHm : R.S.rationalCartierToWeilHom Hm = -((n : ℚ) • Dweil R C P)) (Q : R.S.PrimeCurve) :
    (Q.intersectionNumber Hm : ℚ) = (n : ℚ) * R.S.numericalRestrictionDegree Q (Lnum' R C P) := by
  rw [← numericalRestrictionDegree_cartierClass R.S R.hreg Q Hm, cartierClass_Hm R C P hHm,
    map_smul, smul_eq_mul]

theorem intersectionPairing_Hm {n : ℕ} {Hm : CartierDivisor R.S.toScheme}
    (hHm : R.S.rationalCartierToWeilHom Hm = -((n : ℚ) • Dweil R C P)) :
    (R.S.intersectionPairing R.hreg Hm Hm : ℚ) = (n : ℚ) ^ 2 * Lsq' R C P := by
  rw [← NefNullCurveNegativeSquare.cartierClass_pairing R.S R.hreg Hm Hm, cartierClass_Hm R C P hHm,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  unfold Lsq'
  ring

/-- `#G† + 1 = ρ(S)`: the retained family has `ρ(S) - 1` members. -/
theorem card_famG (p : ℕ) [CharP k p] (hp : 0 < p) :
    Fintype.card (D0 R C ⊕ Unit) + 1 = R.S.picardRank := by
  have h : R.S.picardRank = 1 + Nat.card R.Vertices := by
    have := R.hmin.picardRank_eq_of_klt R.hklt p hp
    rw [R.hrank] at this
    exact this
  have hD0 : Fintype.card (D0 R C) + 1 = Nat.card R.Vertices := by
    rw [Nat.card_eq_fintype_card]
    have h1 : Fintype.card (D0 R C) = Fintype.card {i : R.Vertices // ¬ i = C} :=
      Fintype.card_congr (Equiv.refl _)
    rw [h1, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have hpos : 0 < Fintype.card R.Vertices := Fintype.card_pos_iff.mpr ⟨C⟩
    omega
  rw [Fintype.card_sum, Fintype.card_unit]
  omega

/-- Pairwise intersections of the retained family are at most one (the members of `D₀` by the
SNC property of `D`, and `P · D_i = r_i ≤ 1` by Lemma 4.2). -/
theorem pair_famG (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i) (a b : D0 R C ⊕ Unit) (hab : a ≠ b) :
    R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg (famG R C P a))
      (R.S.primeCurveCartier R.hreg (famG R C P b)) ≤ 1 := by
  have hforest := R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt
  rcases a with i | u <;> rcases b with j | w
  · exact hforest.2.2.2 i.1 j.1 (fun h => hab (congrArg Sum.inl (Subtype.ext h)))
  · have h := pairing_val_P R C P i
    have hle : rvec R C P i ≤ 1 := by
      unfold rvec
      rw [contactVector_eq]
      exact_mod_cast contact_le_one_of_bounded R P hP i.1 (hbdd i.1 i.2)
    have : (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg (famG R C P (Sum.inl i)))
        (R.S.primeCurveCartier R.hreg (famG R C P (Sum.inr w))) : ℚ) ≤ 1 := by
      simp only [famG_inl, famG_inr]
      rw [h]
      exact hle
    exact_mod_cast this
  · have h := pairing_P_val R C P j
    have hle : rvec R C P j ≤ 1 := by
      unfold rvec
      rw [contactVector_eq]
      exact_mod_cast contact_le_one_of_bounded R P hP j.1 (hbdd j.1 j.2)
    have : (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg (famG R C P (Sum.inr u)))
        (R.S.primeCurveCartier R.hreg (famG R C P (Sum.inl j))) : ℚ) ≤ 1 := by
      simp only [famG_inl, famG_inr]
      rw [h]
      exact hle
    exact_mod_cast this
  · exact absurd rfl hab

/-- **Theorem 4.5, contraction clause** (manuscript lines 1001–1006, 1085–1088): a sufficiently
divisible multiple of `L†` contracts `G† = P + D₀` to a rank-one klt del Pezzo surface `X†`;
all conclusions of Theorem 2.6 hold for the family `G†` with coefficients `λ† = (λ₀†, -c)`.
The hypothesis `hacyclic` is the manuscript's assumption that `P + D₀` is an SNC forest (the
intersection bound `≤ 1` is derived, `pair_famG`). -/
theorem anticanonicalContraction_famG (p : ℕ) [CharP k p] (hp : 0 < p)
    (hP : R.IsExteriorMinusOne P) (hexC : IsExcessContact R P C)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i)
    (hacyclic : (curveIncidenceGraph (famG R C P)).IsAcyclic) :
    ∃ (Y : NormalProjectiveSurface k) (f : R.S.toScheme ⟶ Y.toScheme)
      (hproper : IsProper f) (hbir : IsBirationalScheme f),
      f ≫ Y.structureMorphism = R.S.structureMorphism ∧ IsIso f.c ∧ IsBirational f ∧
      (∀ y : Y.toScheme, IsConnected (f.base ⁻¹' {y})) ∧
      (∀ Q : R.S.PrimeCurve, IsExceptionalCurve f Q ↔ ∃ j, Q = famG R C P j) ∧
      IsKltDelPezzo Y ∧ Y.picardRank = 1 ∧
      letI : IsProper f := hproper
      letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      let KY : Y.WeilDivisor :=
        BirationalWeilPushforward.pushforward f hbir (R.S.cartierToWeilHom R.KS)
      IsKltWithCanonicalDivisor Y KY ∧ Y.QAmple (-rationalizeWeilDivisor Y KY) ∧
      ∃ hK : Y.QCartier (rationalizeWeilDivisor Y KY),
        QCartierPullback.pullback f (rationalizeWeilDivisor Y KY) hK =
          R.S.rationalCartierToWeilHom R.KS + ∑ j, Finsupp.single (famG R C P j) (lamG R C P j) := by
  obtain ⟨n, Hm, hn, hHm⟩ := exists_cartier_multiple R C P
  have hinj := famG_injective R C P hP.2
  have hrat : ∀ j, ∃ e : (famG R C P j).toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = (famG R C P j).toSpec := by
    rintro (i | u)
    · exact R.exceptional_rational i.1.1 i.1.2
    · exact hP.1.isoProjectiveLine
  have hlam : ∀ j, lamG R C P j < 1 := by
    rintro (i | u)
    · exact lam0'_lt_one R C P hP hbdd i
    · exact neg_cC_lt_one R C P hP hbdd
  have hHm' : R.S.rationalCartierToWeilHom Hm = -((n : ℚ) • (R.S.rationalCartierToWeilHom R.KS +
      ∑ j, Finsupp.single (famG R C P j) (lamG R C P j))) := hHm
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hnef : Positivity.IsNef R.S.structureMorphism (cartierDivisorInvertibleSheaf R.S.toScheme Hm) := by
    rw [Positivity.isNef_iff_forall_primeCurve]
    intro Q
    rw [← Q.intersectionNumber_eq_restrictionDegree]
    have h1 := intersectionNumber_Hm R C P hHm Q
    have h2 := degree_Lnum'_nonneg R C P p hp hP hexC hbdd Q
    have : (0 : ℚ) ≤ (Q.intersectionNumber Hm : ℚ) := by
      rw [h1]
      exact mul_nonneg hnpos.le h2
    exact_mod_cast this
  have hsq : 0 < R.S.intersectionPairing R.hreg Hm Hm := by
    have h1 := intersectionPairing_Hm R C P hHm
    have h2 := Lsq'_pos R C P p hp hP hexC hbdd
    have : (0 : ℚ) < (R.S.intersectionPairing R.hreg Hm Hm : ℚ) := by
      rw [h1]
      exact mul_pos (pow_pos hnpos 2) h2
    exact_mod_cast this
  have hnull : ∀ Q : R.S.PrimeCurve,
      Q.restrictionDegree (cartierDivisorInvertibleSheaf R.S.toScheme Hm) = 0 ↔
        ∃ j, Q = famG R C P j := by
    intro Q
    rw [← Q.intersectionNumber_eq_restrictionDegree,
      ← degree_Lnum'_eq_zero_iff R C P p hp hP hexC hbdd Q]
    have h1 := intersectionNumber_Hm R C P hHm Q
    constructor
    · intro h0
      have h2 : (n : ℚ) * R.S.numericalRestrictionDegree Q (Lnum' R C P) = 0 := by
        rw [← h1, h0, Int.cast_zero]
      exact (mul_eq_zero.mp h2).resolve_left hnpos.ne'
    · intro h0
      have h2 : (Q.intersectionNumber Hm : ℚ) = 0 := by
        rw [h1, h0, mul_zero]
      exact_mod_cast h2
  exact anticanonicalContraction p hp R.S R.hreg R.KS R.eKS (famG R C P) hinj hrat hacyclic
    (pair_famG R C P hP hbdd) (card_famG R C p hp) (lamG R C P) hlam n hn Hm hHm' hnef hsq hnull

/-! ### (vi) A minimal resolution with strictly fewer exceptional curves -/

/-- A resolution with an exceptional `(-1)`-curve factors through a minimal resolution having
strictly fewer exceptional curves (the union's contraction induction, each step lowering the
count by `IsContraction.ncard_exceptionalCurves_lt_of_actualMaps`). -/
theorem exists_minimalResolution_ncard_lt {S X : NormalProjectiveSurface k}
    {f : S.toScheme ⟶ X.toScheme} (hres : IsResolution S X f) (E : S.PrimeCurve)
    (hE : IsExceptionalCurve f E) (hE1 : IsMinusOneCurve hres.regular E) :
    ∃ (T : NormalProjectiveSurface k) (g : T.toScheme ⟶ X.toScheme),
      IsMinimalResolution T X g ∧
        {Q : T.PrimeCurve | IsExceptionalCurve g Q}.ncard <
          {Q : S.PrimeCurve | IsExceptionalCurve f Q}.ncard := by
  have key := hres.contraction_induction
    (fun T g => ∃ (T₁ : NormalProjectiveSurface k) (g₁ : T₁.toScheme ⟶ X.toScheme),
      IsMinimalResolution T₁ X g₁ ∧
      {Q : T₁.PrimeCurve | IsExceptionalCurve g₁ Q}.ncard ≤
        {Q : T.PrimeCurve | IsExceptionalCurve g Q}.ncard ∧
      (¬ IsMinimalResolution T X g →
        {Q : T₁.PrimeCurve | IsExceptionalCurve g₁ Q}.ncard <
          {Q : T.PrimeCurve | IsExceptionalCurve g Q}.ncard))
    (fun T g hmin => ⟨T, g, hmin, le_rfl, fun h => absurd hmin h⟩)
    (fun T T' g g' hresT hresT' E b hE _ hb hfac ih => by
      obtain ⟨T₁, g₁, hmin₁, hle, -⟩ := ih
      have hlt := hb.ncard_exceptionalCurves_lt_of_actualMaps hresT hresT' hfac hE
      exact ⟨T₁, g₁, hmin₁, le_of_lt (lt_of_le_of_lt hle hlt), fun _ => lt_of_le_of_lt hle hlt⟩)
  obtain ⟨T, g, hmin, -, hlt⟩ := key
  refine ⟨T, g, hmin, hlt ?_⟩
  intro hminf
  exact hminf.no_minusOne_curve E hE hE1

/-- Points of an exceptional curve all map to the image of its generic point. -/
theorem image_eq_of_exceptional {S X : NormalProjectiveSurface k} {f : S.toScheme ⟶ X.toScheme}
    {Q : S.PrimeCurve} (hQ : IsExceptionalCurve f Q) {x : S.toScheme} (hx : x ∈ (Q : Set S.toScheme)) :
    f.base x = f.base Q.genericPoint := by
  obtain ⟨z, hz⟩ := hQ
  have h1 : f.base x ∈ ({z} : Set X.toScheme) := hz ▸ Set.mem_image_of_mem _ hx
  have h2 : f.base Q.genericPoint ∈ ({z} : Set X.toScheme) :=
    hz ▸ Set.mem_image_of_mem _ Q.genericPoint_mem
  rw [Set.mem_singleton_iff] at h1 h2
  rw [h1, h2]

/-! ### Graph counts: `s_C`, `a`, and the components of `P + D₀` -/

/-- The manuscript's `a`: the number of components of `D₀` met by `P` (for the SNC forest
`P + D₀` these are the `D_i` with `r_i ≠ 0`, one per contacted component). -/
def contactCount : ℕ := (Finset.univ.filter (fun i : D0 R C => rvec R C P i ≠ 0)).card

theorem contactCount_eq_zero_iff : contactCount R C P = 0 ↔ ∀ i : D0 R C, rvec R C P i = 0 := by
  unfold contactCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [Finset.mem_univ, true_implies, not_not]

/-- `s_C = #π₀(Γ − C) − (#π₀(D) − 1)`: deleting `C` from the exceptional forest `D` replaces its
component by `degree C` pieces (manuscript line 1034, `s_C := #π₀(Γ − C) = deg C`). -/
theorem card_components_induce_compl [DecidableRel R.graph.Adj] :
    Nat.card (SimpleGraph.induce ({C}ᶜ : Set R.Vertices) R.graph).ConnectedComponent + 1 =
      Nat.card R.graph.ConnectedComponent + R.graph.degree C := by
  have hac : R.graph.IsAcyclic := (R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt).2.2.1
  have h := KltDP.Support.WeightedForestCore.deleteVertex_card_components R.graph hac C
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  exact h

/-- The induced graph of `P + D₀` on `D₀` is the induced graph of `D` on `D − C`. -/
def induceIso : SimpleGraph.induce ({C}ᶜ : Set R.Vertices) R.graph ≃g
    SimpleGraph.induce ({Sum.inr ()}ᶜ : Set (D0 R C ⊕ Unit)) (curveIncidenceGraph (famG R C P)) := by
  let g : ↥({C}ᶜ : Set R.Vertices) → ↥({Sum.inr ()}ᶜ : Set (D0 R C ⊕ Unit)) :=
    fun v => ⟨Sum.inl ⟨v.1, v.2⟩, Sum.inl_ne_inr⟩
  have hg : Function.Bijective g := by
    constructor
    · intro v w h
      have h' : Sum.inl (⟨v.1, v.2⟩ : D0 R C) = Sum.inl ⟨w.1, w.2⟩ := congrArg Subtype.val h
      exact Subtype.ext (congrArg Subtype.val (Sum.inl_injective h'))
    · rintro ⟨x, hx⟩
      rcases x with i | u
      · exact ⟨⟨i.1, i.2⟩, rfl⟩
      · exact absurd rfl (by cases u; exact hx)
  refine ⟨Equiv.ofBijective g hg, ?_⟩
  intro v w
  show (Sum.inl (⟨v.1, v.2⟩ : D0 R C) ≠ Sum.inl ⟨w.1, w.2⟩ ∧
      ((v.1.1 : Set R.S.toScheme) ∩ w.1.1).Nonempty) ↔
    (v.1 ≠ w.1 ∧ ((v.1.1 : Set R.S.toScheme) ∩ w.1.1).Nonempty)
  refine and_congr ?_ Iff.rfl
  constructor
  · intro h1 h2
    exact h1 (by rw [Subtype.ext h2])
  · intro h1 h2
    exact h1 (congrArg Subtype.val (Sum.inl_injective h2))

/-- The degree of `P` in the incidence graph of `P + D₀` is `a`. -/
theorem degree_inr_eq_contactCount (hP : ¬ IsExceptionalCurve R.π P)
    [DecidableRel (curveIncidenceGraph (famG R C P)).Adj] :
    (curveIncidenceGraph (famG R C P)).degree (Sum.inr ()) = contactCount R C P := by
  have hinj := famG_injective R C P hP
  unfold contactCount
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have hfilter : (Finset.univ.filter (fun x => (curveIncidenceGraph (famG R C P)).Adj (Sum.inr ()) x)) =
      (Finset.univ.filter (fun i : D0 R C => rvec R C P i ≠ 0)).map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext x
    rcases x with i | u
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk, Sum.inl.injEq, exists_eq_right]
      rw [curveIncidenceGraph_adj_iff_pairing_pos R.S R.hreg (famG R C P) hinj]
      have h := pairing_P_val R C P i
      simp only [famG_inl, famG_inr]
      constructor
      · rintro ⟨-, hpos⟩
        have : (0 : ℚ) < rvec R C P i := by
          rw [← h]
          exact_mod_cast hpos
        exact this.ne'
      · intro hne
        refine ⟨Sum.inr_ne_inl, ?_⟩
        have h0 := rvec_nonneg R C P hP i
        have : (0 : ℚ) < rvec R C P i := lt_of_le_of_ne h0 (Ne.symm hne)
        rw [← h] at this
        exact_mod_cast this
    · cases u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk, reduceCtorEq, and_false, exists_false, iff_false]
      exact (curveIncidenceGraph (famG R C P)).loopless _
  rw [hfilter, Finset.card_map]

/-- `#π₀(P + D₀) + a = #π₀(D) + deg C` (the component bookkeeping of manuscript lines 1099–1109). -/
theorem card_components_famG [DecidableRel R.graph.Adj] (hP : ¬ IsExceptionalCurve R.π P)
    (hacyclic : (curveIncidenceGraph (famG R C P)).IsAcyclic) :
    Nat.card (curveIncidenceGraph (famG R C P)).ConnectedComponent + contactCount R C P =
      Nat.card R.graph.ConnectedComponent + R.graph.degree C := by
  classical
  have hdel := KltDP.Support.WeightedForestCore.deleteVertex_card_components
    (curveIncidenceGraph (famG R C P)) hacyclic (Sum.inr ())
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    degree_inr_eq_contactCount R C P hP] at hdel
  have hΓ : Nat.card (SimpleGraph.induce ({C}ᶜ : Set R.Vertices) R.graph).ConnectedComponent =
      Nat.card (SimpleGraph.induce ({Sum.inr ()}ᶜ : Set (D0 R C ⊕ Unit))
        (curveIncidenceGraph (famG R C P))).ConnectedComponent :=
    Nat.card_congr (induceIso R C P).connectedComponentEquiv
  have hD := card_components_induce_compl R C
  omega

/-! ### (vii) The singular points of `X†` -/

section Contraction

variable (Y : NormalProjectiveSurface k) (f : R.S.toScheme ⟶ Y.toScheme) [IsProper f]
  (hbir : IsBirationalScheme f) (hf : f ≫ Y.structureMorphism = R.S.structureMorphism)
  (hconn : ∀ y : Y.toScheme, IsConnected (f.base ⁻¹' {y}))
  (hexc : ∀ Q : R.S.PrimeCurve, IsExceptionalCurve f Q ↔ ∃ j, Q = famG R C P j)

include hexc in
theorem exceptional_famG (j : D0 R C ⊕ Unit) : IsExceptionalCurve f (famG R C P j) :=
  (hexc _).mpr ⟨j, rfl⟩

include hbir hf hconn hexc in
/-- The component count of the exceptional locus of `f` is the component count of the
incidence graph of `P + D₀`. -/
theorem ncard_imagePoints (hP : ¬ IsExceptionalCurve R.π P) :
    (ActualExceptionalLocus.imagePoints f).ncard =
      Nat.card (curveIncidenceGraph (famG R C P)).ConnectedComponent := by
  have hinj := famG_injective R C P hP
  let eV : D0 R C ⊕ Unit ≃ ActualExceptionalIncidence.Vertices f :=
    Equiv.ofBijective (fun j => ⟨famG R C P j, exceptional_famG R C P Y f hexc j⟩)
      ⟨fun a b h => hinj (congrArg Subtype.val h),
       fun v => by
        obtain ⟨j, hj⟩ := (hexc v.1).mp v.2
        exact ⟨j, Subtype.ext hj.symm⟩⟩
  let eG : curveIncidenceGraph (famG R C P) ≃g ActualExceptionalIncidence.graph f := by
    refine ⟨eV, ?_⟩
    intro a b
    show (eV a ≠ eV b ∧ ((famG R C P a : Set R.S.toScheme) ∩ famG R C P b).Nonempty) ↔
      (a ≠ b ∧ ((famG R C P a : Set R.S.toScheme) ∩ famG R C P b).Nonempty)
    exact and_congr eV.injective.ne_iff Iff.rfl
  rw [← ActualExceptionalLocus.component_count f hbir hf hconn,
    Nat.card_congr (ActualExceptionalIncidence.supportComponentEquiv f hbir)]
  exact Nat.card_congr eG.connectedComponentEquiv.symm

include hbir hf hconn in
/-- Every singular point of `X†` is the image of a contracted curve (`f` is an isomorphism off
the image of `P + D₀`). -/
theorem singularPoints_subset_imagePoints [IsIso f.c] :
    (Y.singularPoints : Set Y.Point) ⊆ ActualExceptionalLocus.imagePoints f := by
  letI : IsIso (f ∣_ ActualExceptionalLocus.complementOpen f hbir) :=
    ActualExceptionalLocus.isIso_complementOpen f hbir hf hconn
  have h := RegularPointsOnIsomorphismOpen.singularPoints_subset_compl Y f
    (ActualExceptionalLocus.complementOpen f hbir) R.hreg
  intro y hy
  have hy' := h hy
  exact not_not.mp hy'

include hbir hf hexc in
/-- The image of each retained component `D_i ⊂ D₀` is a singular point of `X†`: its discrepancy
coefficient `-λ†_i ≤ 0` (the manuscript's "each surviving component ... has a singular image",
lines 1107–1109; via `RegularTargetCanonicalDiscrepancy.coefficient_pos_of_regular_closed_image`). -/
theorem image_val_mem_singularPoints (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i)
    (hK : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      Y.QCartier (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (R.S.cartierToWeilHom R.KS))))
    (hpull : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      QCartierPullback.pullback f (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (R.S.cartierToWeilHom R.KS))) hK =
        R.S.rationalCartierToWeilHom R.KS + ∑ j, Finsupp.single (famG R C P j) (lamG R C P j))
    (i : D0 R C) : f.base i.1.1.genericPoint ∈ Y.singularPoints := by
  letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
  have hexci : IsExceptionalCurve f i.1.1 := exceptional_famG R C P Y f hexc (Sum.inl i)
  have hmem : f.base i.1.1.genericPoint ∈ ActualExceptionalLocus.imagePoints f :=
    ⟨_, (ActualExceptionalLocus.mem_primeSupport f _).mpr ⟨i.1.1, hexci, i.1.1.genericPoint_mem⟩, rfl⟩
  have hclosed : IsClosed ({f.base i.1.1.genericPoint} : Set Y.toScheme) :=
    ActualExceptionalLocus.imagePoint_isClosed f ⟨_, hmem⟩
  have hKYcan := isCanonicalWeilDivisor_pushforward_of_cartier R.S Y f hf hbir R.KS R.eKS
  rw [Y.mem_singularPoints]
  intro hreg
  have hpos := RegularTargetCanonicalDiscrepancy.coefficient_pos_of_regular_closed_image R.S Y f
    hbir hf R.KS R.eKS _ hKYcan hK rfl i.1.1 hclosed hreg
  rw [hpull] at hpos
  have hval : (∑ j, Finsupp.single (famG R C P j) (lamG R C P j)) i.1.1 = lam0' R C P i := by
    have h := sum_single_apply_eq (famG R C P) (famG_injective R C P hP.2) (lamG R C P) (Sum.inl i)
    simpa using h
  simp only [Finsupp.sub_apply, Finsupp.add_apply, hval] at hpos
  linarith [lam0'_nonneg R C P hP hbdd i]

include hexc in
/-- The image of the exceptional locus of `f` is `f(D₀) ∪ {f(P)}`. -/
theorem imagePoints_eq :
    ActualExceptionalLocus.imagePoints f =
      Set.range (fun i : D0 R C => f.base i.1.1.genericPoint) ∪ {f.base P.genericPoint} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨Q, hQ, hxQ⟩ := (ActualExceptionalLocus.mem_primeSupport f x).mp hx
    obtain ⟨j, rfl⟩ := (hexc Q).mp hQ
    rcases j with i | u
    · exact Or.inl ⟨i, (image_eq_of_exceptional hQ hxQ).symm⟩
    · exact Or.inr (image_eq_of_exceptional hQ hxQ)
  · rintro (⟨i, rfl⟩ | hy)
    · exact ⟨_, (ActualExceptionalLocus.mem_primeSupport f _).mpr
        ⟨i.1.1, exceptional_famG R C P Y f hexc (Sum.inl i), i.1.1.genericPoint_mem⟩, rfl⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ⟨_, (ActualExceptionalLocus.mem_primeSupport f _).mpr
        ⟨P, exceptional_famG R C P Y f hexc (Sum.inr ()), P.genericPoint_mem⟩, rfl⟩

include hbir hf hconn hexc in
/-- When `P` meets no component of `D₀` (`r = 0`), the contracted `P` gives a regular point of
`X†` (manuscript lines 1105–1106): `f` factors through the Castelnuovo contraction `σ` of `P`,
the fibre of `f` over `f(P)` is exactly `P`, so the induced `S₁ → X†` is an isomorphism near
`σ(P)`, a regular point. -/
theorem image_P_regular (hP : R.IsExteriorMinusOne P) (hr0 : ∀ i : D0 R C, rvec R C P i = 0)
    (hres : IsResolution R.S Y f) : RegularPoint Y.toScheme (f.base P.genericPoint) := by
  have hPexc : IsExceptionalCurve f P := exceptional_famG R C P Y f hexc (Sum.inr ())
  -- `P` is disjoint from every `D_i`
  have hdisj : ∀ i : D0 R C, Disjoint (P : Set R.S.toScheme) (i.1.1 : Set R.S.toScheme) := by
    intro i
    have hne : P ≠ i.1.1 := fun h => hP.2 (by rw [h]; exact i.1.2)
    have h0 : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg P)
        (R.S.primeCurveCartier R.hreg i.1.1) = 0 := by
      have := pairing_P_val R C P i
      rw [hr0 i] at this
      exact_mod_cast this
    exact (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
      R.S R.hreg P i.1.1 hne).mp h0
  -- the fibre of `f` over `f(P)` is exactly `P`
  have hfib : f.base ⁻¹' {f.base P.genericPoint} = (P : Set R.S.toScheme) := by
    apply Set.Subset.antisymm
    · intro x hx
      have hx' : x ∈ ActualExceptionalLocus.primeSupport f := by
        rw [← ActualExceptionalLocus.preimage_image_primeSupport f hbir hf hconn]
        show f.base x ∈ ActualExceptionalLocus.imagePoints f
        rw [show f.base x = f.base P.genericPoint from hx]
        exact ⟨_, (ActualExceptionalLocus.mem_primeSupport f _).mpr
          ⟨P, hPexc, P.genericPoint_mem⟩, rfl⟩
      obtain ⟨Q, hQ, hxQ⟩ := (ActualExceptionalLocus.mem_primeSupport f x).mp hx'
      obtain ⟨j, rfl⟩ := (hexc Q).mp hQ
      rcases j with i | u
      · exfalso
        -- the connected fibre would be split by the disjoint closed sets `P` and `⋃ D_j`
        have hF := hconn (f.base P.genericPoint)
        set F := f.base ⁻¹' {f.base P.genericPoint} with hFdef
        let E : Set R.S.toScheme := ⋃ j : D0 R C, (j.1.1 : Set R.S.toScheme)
        have hEclosed : IsClosed E := isClosed_iUnion_of_finite (fun j => j.1.1.isClosed)
        have hFsub : F ⊆ (P : Set R.S.toScheme) ∪ E := by
          intro t ht
          have ht' : t ∈ ActualExceptionalLocus.primeSupport f := by
            rw [← ActualExceptionalLocus.preimage_image_primeSupport f hbir hf hconn]
            show f.base t ∈ ActualExceptionalLocus.imagePoints f
            rw [show f.base t = f.base P.genericPoint from ht]
            exact ⟨_, (ActualExceptionalLocus.mem_primeSupport f _).mpr
              ⟨P, hPexc, P.genericPoint_mem⟩, rfl⟩
          obtain ⟨Q', hQ', htQ'⟩ := (ActualExceptionalLocus.mem_primeSupport f t).mp ht'
          obtain ⟨j', rfl⟩ := (hexc Q').mp hQ'
          rcases j' with i' | u'
          · exact Or.inr (Set.mem_iUnion.mpr ⟨i', htQ'⟩)
          · exact Or.inl htQ'
        have hPE : (P : Set R.S.toScheme) ∩ E = ∅ := by
          apply Set.eq_empty_of_forall_not_mem
          rintro t ⟨htP, htE⟩
          obtain ⟨j, htj⟩ := Set.mem_iUnion.mp htE
          exact (Set.disjoint_left.mp (hdisj j)) htP htj
        have hFinter : F ∩ ((P : Set R.S.toScheme) ∩ E) = ∅ := by
          rw [hPE, Set.inter_empty]
        rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hF.isPreconnected
          (P : Set R.S.toScheme) E P.isClosed hEclosed hFsub hFinter) with hFP | hFE
        · exact (Set.disjoint_left.mp (hdisj i)) (hFP hx) hxQ
        · have hgen : P.genericPoint ∈ F := by
            show f.base P.genericPoint ∈ ({f.base P.genericPoint} : Set Y.toScheme)
            exact rfl
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hFE hgen)
          exact (Set.disjoint_left.mp (hdisj j)) P.genericPoint_mem hj
      · exact hxQ
    · intro x hx
      exact image_eq_of_exceptional hPexc hx
  -- the Castelnuovo contraction of `P` and the induced resolution
  obtain ⟨S', σ, hσ⟩ := (GeneralResolution.contraction k).exists_contraction R.S R.hreg P hP.1
  obtain ⟨g', hfac, hres'⟩ := hres.of_contraction (contractionUniversal k) hσ hPexc
  obtain ⟨z, -, hzfib, -⟩ := hσ.centerFiber_eq_curve
  have hsurj : Function.Surjective σ.base := by
    letI : IsIntegral R.S.toScheme := R.S.integral
    letI : IsIntegral S'.toScheme := S'.integral
    letI : IsProper σ := hσ.isProper
    letI : GenericPointPreserving σ := ⟨hσ.birational.map_genericPoint⟩
    obtain ⟨h⟩ := surjective_of_proper_genericPointPreserving σ
    exact h
  have hcomp : ∀ x : R.S.toScheme, f.base x = g'.base (σ.base x) := by
    intro x
    rw [← hfac, Scheme.comp_base_apply]
  have hzP : σ.base P.genericPoint = z := by
    have : P.genericPoint ∈ σ.base ⁻¹' {z} := by
      rw [hzfib]
      exact P.genericPoint_mem
    exact this
  have hyz : f.base P.genericPoint = g'.base z := by
    rw [hcomp, hzP]
  -- the fibre of `g'` over `f(P)` is `{z}`
  have hfib' : g'.base ⁻¹' {f.base P.genericPoint} = {z} := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, rfl⟩ := hsurj w
      have hx : x ∈ f.base ⁻¹' {f.base P.genericPoint} := by
        show f.base x ∈ ({f.base P.genericPoint} : Set Y.toScheme)
        rw [hcomp x]
        exact hw
      rw [hfib] at hx
      have : x ∈ σ.base ⁻¹' {z} := by
        rw [hzfib]
        exact hx
      exact this
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      show g'.base z ∈ ({f.base P.genericPoint} : Set Y.toScheme)
      rw [hyz]
      rfl
  -- connected fibres of `g'`
  have hconn' : ∀ y : Y.toScheme, IsConnected (g'.base ⁻¹' {y}) := by
    intro y
    have : g'.base ⁻¹' {y} = σ.base '' (f.base ⁻¹' {y}) := by
      have hpre : f.base ⁻¹' {y} = σ.base ⁻¹' (g'.base ⁻¹' {y}) := by
        ext x
        show f.base x ∈ ({y} : Set Y.toScheme) ↔ g'.base (σ.base x) ∈ ({y} : Set Y.toScheme)
        rw [hcomp]
      rw [hpre, Set.image_preimage_eq _ hsurj]
    rw [this]
    exact (hconn y).image _ σ.continuous.continuousOn
  -- `f(P)` is not in the image of the exceptional locus of `g'`
  letI : IsProper g' := hres'.isProper
  have hbir' : IsBirationalScheme g' :=
    (isBirational_iff_isBirationalScheme g').mp hres'.birational
  have hnot : f.base P.genericPoint ∉ ActualExceptionalLocus.imagePoints g' := by
    rintro ⟨w, hw, hwy⟩
    have hwz : w = z := by
      have : w ∈ g'.base ⁻¹' {f.base P.genericPoint} := hwy
      rw [hfib'] at this
      exact this
    obtain ⟨Q', hQ', hwQ'⟩ := (ActualExceptionalLocus.mem_primeSupport g' w).mp hw
    obtain ⟨y', hy'⟩ := hQ'
    have hQsub : (Q' : Set S'.toScheme) ⊆ {z} := by
      intro t ht
      have h1 : g'.base t ∈ ({y'} : Set Y.toScheme) := hy' ▸ Set.mem_image_of_mem _ ht
      have h2 : g'.base w ∈ ({y'} : Set Y.toScheme) := hy' ▸ Set.mem_image_of_mem _ hwQ'
      rw [Set.mem_singleton_iff] at h1 h2
      have : t ∈ g'.base ⁻¹' {f.base P.genericPoint} := by
        show g'.base t ∈ ({f.base P.genericPoint} : Set Y.toScheme)
        rw [h1, ← h2, hwy]
        rfl
      rwa [hfib'] at this
    haveI : Subsingleton (Q' : Set S'.toScheme) :=
      (Set.subsingleton_of_subset_singleton hQsub).coe_sort
    have hle := topologicalKrullDim_nonpos_of_subsingleton (Q' : Set S'.toScheme)
    rw [Q'.dimension_one] at hle
    exact (WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 1)).not_le hle
  letI : IsIso g'.c := ProperBirationalStructureSheaf.resolution_c_isIso g' hres'
  letI : IsIso (g' ∣_ ActualExceptionalLocus.complementOpen g' hbir') :=
    ActualExceptionalLocus.isIso_complementOpen g' hbir' hres'.over_base hconn'
  exact RegularPointsOnIsomorphismOpen.regularPoint_of_mem g'
    (ActualExceptionalLocus.complementOpen g' hbir') hσ.regular _ hnot

include hbir hf hconn hexc in
/-- **The singular-point count of `X†`** (manuscript eq:replacement-component-count, lines
1035–1041 and 1099–1109), in the form `#Sing(X†) + a = #Sing(X) + deg C` when `a ≥ 1` and
`#Sing(X†) + 1 = #Sing(X) + deg C` when `a = 0`; uniformly
`#Sing(X†) = #Sing(X) + countChange (deg C) a` with `countChange s a = s - max a 1`. -/
theorem singularPoints_card_eq [DecidableRel R.graph.Adj] [IsIso f.c]
    (hP : R.IsExteriorMinusOne P)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i)
    (hacyclic : (curveIncidenceGraph (famG R C P)).IsAcyclic)
    (hres : IsResolution R.S Y f)
    (hK : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      Y.QCartier (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (R.S.cartierToWeilHom R.KS))))
    (hpull : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      QCartierPullback.pullback f (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (R.S.cartierToWeilHom R.KS))) hK =
        R.S.rationalCartierToWeilHom R.KS + ∑ j, Finsupp.single (famG R C P j) (lamG R C P j)) :
    (Y.singularPoints.card : ℤ) =
      R.X.singularPoints.card + KltDP.Support.countChange (R.graph.degree C) (contactCount R C P) := by
  have hnX : R.X.singularPoints.card = Nat.card R.graph.ConnectedComponent :=
    (R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt).2.1
  have hcomp := card_components_famG R C P hP.2 hacyclic
  have himg := ncard_imagePoints R C P Y f hbir hf hconn hexc hP.2
  have hsub1 := singularPoints_subset_imagePoints R Y f hbir hf hconn
  have hsub2 := image_val_mem_singularPoints R C P Y f hbir hf hexc hP hbdd hK hpull
  have hset := imagePoints_eq R C P Y f hexc
  have hPexc : IsExceptionalCurve f P := exceptional_famG R C P Y f hexc (Sum.inr ())
  have hyP_mem : f.base P.genericPoint ∈ ActualExceptionalLocus.imagePoints f := by
    rw [hset]
    exact Or.inr rfl
  by_cases ha : ∀ i : D0 R C, rvec R C P i = 0
  · -- `a = 0`: the contracted `P` is a regular point
    have ha0 : contactCount R C P = 0 := (contactCount_eq_zero_iff R C P).mpr ha
    have hreg := image_P_regular R C P Y f hbir hf hconn hexc hP ha hres
    have hnotsing : f.base P.genericPoint ∉ Y.singularPoints := by
      rw [Y.mem_singularPoints]
      exact not_not.mpr hreg
    have hsing : (Y.singularPoints : Set Y.Point) =
        ActualExceptionalLocus.imagePoints f \ {f.base P.genericPoint} := by
      ext y
      constructor
      · intro hy
        refine ⟨hsub1 hy, ?_⟩
        rw [Set.mem_singleton_iff]
        rintro rfl
        exact hnotsing hy
      · rintro ⟨hy, hne⟩
        rw [hset] at hy
        rcases hy with ⟨i, rfl⟩ | hy
        · exact hsub2 i
        · exact absurd hy hne
    have hcard : Y.singularPoints.card = (ActualExceptionalLocus.imagePoints f).ncard - 1 := by
      rw [← Set.ncard_coe_Finset, hsing,
        Set.ncard_diff_singleton_of_mem hyP_mem (ActualExceptionalLocus.imagePoints_finite f hbir)]
    have hpos : 0 < (ActualExceptionalLocus.imagePoints f).ncard :=
      (Set.ncard_pos (ActualExceptionalLocus.imagePoints_finite f hbir)).mpr ⟨_, hyP_mem⟩
    rw [ha0, KltDP.Support.countChange_zero, hcard, hnX]
    rw [himg] at hpos ⊢
    rw [ha0] at hcomp
    omega
  · -- `a ≥ 1`: `f(P)` is the image of a contacted component, hence singular
    push_neg at ha
    obtain ⟨i₀, hi₀⟩ := ha
    have ha1 : 1 ≤ contactCount R C P := by
      unfold contactCount
      exact Finset.card_pos.mpr ⟨i₀, by simp [hi₀]⟩
    have hyP : f.base P.genericPoint = f.base i₀.1.1.genericPoint := by
      have hne : P ≠ i₀.1.1 := fun h => hP.2 (by rw [h]; exact i₀.1.2)
      have hint : ((P : Set R.S.toScheme) ∩ i₀.1.1).Nonempty := by
        rw [← Set.not_disjoint_iff_nonempty_inter]
        intro hd
        apply hi₀
        have h0 := (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
          R.S R.hreg P i₀.1.1 hne).mpr hd
        have h := pairing_P_val R C P i₀
        rw [← h, h0]
        rfl
      obtain ⟨x, hxP, hxD⟩ := hint
      rw [← image_eq_of_exceptional hPexc hxP,
        image_eq_of_exceptional (exceptional_famG R C P Y f hexc (Sum.inl i₀)) hxD, famG_inl]
    have hsing : (Y.singularPoints : Set Y.Point) = ActualExceptionalLocus.imagePoints f := by
      apply Set.Subset.antisymm hsub1
      intro y hy
      rw [hset] at hy
      rcases hy with ⟨i, rfl⟩ | hy
      · exact hsub2 i
      · rw [Set.mem_singleton_iff] at hy
        rw [hy, hyP]
        exact hsub2 i₀
    have hcard : Y.singularPoints.card = (ActualExceptionalLocus.imagePoints f).ncard := by
      rw [← Set.ncard_coe_Finset, hsing]
    rw [KltDP.Support.countChange_pos _ _ ha1, hcard, hnX, himg]
    omega

end Contraction

/-! ### The replacement datum -/

/-- **Manuscript Theorem 4.5, datum form** (`thm:one-component-replacement`, lines 990–1111).
Let `R` be a resolution datum, `P` an exterior `(-1)`-curve whose only excess contact is the
exceptional component `C` (`hexC`, `hbdd`), and assume `P + D₀` is an SNC forest (`hacyclic`;
the pairwise intersection bound is derived). Then the rank-one klt del Pezzo surface `X†` obtained
by contracting `P + D₀` (Theorem 2.6 applied to `L†`) carries a resolution datum `R₁` with
`ρ(R₁.S) < ρ(R.S)` and
`#Sing(X†) = #Sing(X) + countChange (deg C) a`, i.e. `#Sing(X†) - #Sing(X) = s_C - a` when
`a ≥ 1` and `= s_C - 1` when `a = 0`, where `s_C = deg_D C = #π₀(Γ - C)` and `a` is the number of
components of `D₀` met by `P`. -/
theorem oneComponentReplacement_datum [DecidableRel R.graph.Adj] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hP : R.IsExteriorMinusOne P) (hexC : IsExcessContact R P C)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i)
    (hacyclic : (curveIncidenceGraph (famG R C P)).IsAcyclic) :
    ∃ R₁ : ResolutionDatum k, R₁.S.picardRank < R.S.picardRank ∧
      (R₁.X.singularPoints.card : ℤ) =
        R.X.singularPoints.card + KltDP.Support.countChange (R.graph.degree C) (contactCount R C P) := by
  obtain ⟨Y, f, hproper, hbir, hf, hc, hbirational, hconn, hexc, hDP, hrankY, hrest⟩ :=
    anticanonicalContraction_famG R C P p hp hP hexC hbdd hacyclic
  letI : IsProper f := hproper
  letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
  letI : IsIso f.c := hc
  obtain ⟨hKY, -, hK, hpull⟩ := hrest
  have hres : IsResolution R.S Y f := ⟨hf, R.hreg, hbirational⟩
  have hPexc : IsExceptionalCurve f P := (hexc P).mpr ⟨Sum.inr (), rfl⟩
  obtain ⟨T, g, hmin, hlt⟩ := exists_minimalResolution_ncard_lt hres P hPexc hP.1
  let R₁ : ResolutionDatum k := ⟨T, Y, g, hmin, hDP, hrankY⟩
  refine ⟨R₁, ?_, ?_⟩
  · show T.picardRank < R.S.picardRank
    have h1 : T.picardRank = 1 + Nat.card (ActualExceptionalIncidence.Vertices g) := by
      have := hmin.picardRank_eq_of_klt ⟨_, hKY⟩ p hp
      rw [hrankY] at this
      exact this
    have h2 : Nat.card (ActualExceptionalIncidence.Vertices g) =
        {Q : T.PrimeCurve | IsExceptionalCurve g Q}.ncard := Set.Nat.card_coe_set_eq _
    have h3 : {Q : R.S.PrimeCurve | IsExceptionalCurve f Q}.ncard = Fintype.card (D0 R C ⊕ Unit) := by
      rw [← Set.Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
      have hinj := famG_injective R C P hP.2
      let eV : D0 R C ⊕ Unit ≃ {Q : R.S.PrimeCurve | IsExceptionalCurve f Q} :=
        Equiv.ofBijective (fun j => ⟨famG R C P j, (hexc _).mpr ⟨j, rfl⟩⟩)
          ⟨fun a b h => hinj (congrArg Subtype.val h),
           fun v => by
            obtain ⟨j, hj⟩ := (hexc v.1).mp v.2
            exact ⟨j, Subtype.ext hj.symm⟩⟩
      exact Nat.card_congr eV.symm
    have h4 := card_famG R C p hp
    omega
  · show (Y.singularPoints.card : ℤ) = _
    exact singularPoints_card_eq R C P Y f hbir hf hconn hexc hP hbdd hacyclic hres hK hpull

/-- The two cases of eq:replacement-component-count. -/
theorem oneComponentReplacement_datum_cases [DecidableRel R.graph.Adj] (p : ℕ) [CharP k p]
    (hp : 0 < p) (hP : R.IsExteriorMinusOne P) (hexC : IsExcessContact R P C)
    (hbdd : ∀ i : R.Vertices, i ≠ C → IsBoundedContact R P i)
    (hacyclic : (curveIncidenceGraph (famG R C P)).IsAcyclic) :
    ∃ R₁ : ResolutionDatum k, R₁.S.picardRank < R.S.picardRank ∧
      ((contactCount R C P = 0 →
        (R₁.X.singularPoints.card : ℤ) = R.X.singularPoints.card + (R.graph.degree C - 1)) ∧
       (1 ≤ contactCount R C P →
        (R₁.X.singularPoints.card : ℤ) =
          R.X.singularPoints.card + (R.graph.degree C - contactCount R C P))) := by
  obtain ⟨R₁, hρ, hcount⟩ := oneComponentReplacement_datum R C P p hp hP hexC hbdd hacyclic
  refine ⟨R₁, hρ, fun h0 => ?_, fun h1 => ?_⟩
  · rw [hcount, h0, KltDP.Support.countChange_zero]
  · rw [hcount, KltDP.Support.countChange_pos _ _ h1]

end Replacement

end KltDP.Manuscript.S04

#print axioms KltDP.Manuscript.S04.Replacement.rankOne_mulVec_lam0'
#print axioms KltDP.Manuscript.S04.Replacement.energy
#print axioms KltDP.Manuscript.S04.Replacement.negIntersectionMatrix_famG_mulVec_lamG
#print axioms KltDP.Manuscript.S04.Replacement.Lsq'_sub_Lsq
#print axioms KltDP.Manuscript.S04.Replacement.degree_C_pos
#print axioms KltDP.Manuscript.S04.Replacement.degree_Lnum'_eq_zero_iff
#print axioms KltDP.Manuscript.S04.Replacement.anticanonicalContraction_famG
#print axioms KltDP.Manuscript.S04.Replacement.image_P_regular
#print axioms KltDP.Manuscript.S04.Replacement.singularPoints_card_eq
#print axioms KltDP.Manuscript.S04.Replacement.oneComponentReplacement_datum
#print axioms KltDP.Manuscript.S04.Replacement.oneComponentReplacement_datum_cases
