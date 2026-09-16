import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic

/-!
# Negative definiteness from semi-definiteness and non-degeneracy (no geometry)

Pure linear algebra over an ordered field, with no scheme theory, so that lanes A2 and F can import
it without pulling in surface theory. `B` is a symmetric bilinear form on a module `M` over a linear
ordered field `K`, and `S : Set M` is any family (in the application, the classes of the exceptional
curves of a resolution).

* `NegSemidefiniteOn B S` : `B x x ≤ 0` for every `x` in the span of `S`;
* `NondegenerateOn B S` : every nonzero `x` in the span of `S` pairs nontrivially with some element
  of the span;
* `pairing_eq_zero_of_self_eq_zero` : the Cauchy–Schwarz kernel property — for a negative
  semi-definite form, a vector of zero square is orthogonal to everything in the span. Proved by the
  discriminant trick, with no analysis;
* **`negDefinite_of_semidefiniteOn_of_nondegenerateOn`** : semi-definite plus non-degenerate on the
  span gives `B x x < 0` for every nonzero `x` there.

**On the shape of this statement.** The tempting shorter hypothesis — "there is a vector `h` with
`B h h ≥ 0` orthogonal to `S`, and `B` is non-degenerate" — does **not** imply negative definiteness
on `S`, and this module deliberately does not assume it. Counterexample (recorded as
`not_negDefinite_of_orthogonal_nonneg_square`, proved below so the record cannot rot): on `K²` with
the identity form, which is symmetric and non-degenerate, `h = (1, 0)` satisfies `B h h = 1 ≥ 0` and
is orthogonal to `e = (0, 1)`, yet `B e e = 1 > 0`. What is missing is the signature condition: being
orthogonal to a positive-square vector bounds the form only when the ambient form has at most one
positive direction. That is why semi-definiteness appears as a hypothesis here and, in the geometric
wrapper, as a separately named input rather than something derived from orthogonality to pullbacks.
-/

namespace KltDP.Support.NegativeDefinite

open LinearMap (BilinForm)

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M]

/-- `B` is negative semi-definite on the span of `S`. -/
def NegSemidefiniteOn (B : BilinForm K M) (S : Set M) : Prop :=
  ∀ x ∈ Submodule.span K S, B x x ≤ 0

/-- `B` is non-degenerate on the span of `S`: no nonzero vector of the span is orthogonal to the
whole span. -/
def NondegenerateOn (B : BilinForm K M) (S : Set M) : Prop :=
  ∀ x ∈ Submodule.span K S, x ≠ 0 → ∃ w ∈ Submodule.span K S, B x w ≠ 0

/-- Scalar core of the discriminant argument, with no bilinear form in sight: if `d ≤ 0` and the
quadratic `t ↦ 2tc + t²d` is everywhere `≤ 0`, then `c = 0`. The witness `t = c/(1 - d)` is legal
because `d ≤ 0` forces `1 - d > 0`, and it gives `2tc + t²d = c²(2 - d)/(1 - d)² > 0` when `c ≠ 0`. -/
theorem eq_zero_of_quadratic_nonpos {c d : K} (hd : d ≤ 0)
    (h : ∀ t : K, 2 * t * c + t ^ 2 * d ≤ 0) : c = 0 := by
  by_contra hc
  have h1d : (0 : K) < 1 - d := by linarith
  have hne : (1 - d) ≠ 0 := ne_of_gt h1d
  have ht := h (c / (1 - d))
  have hval : 2 * (c / (1 - d)) * c + (c / (1 - d)) ^ 2 * d
      = c ^ 2 * (2 - d) / (1 - d) ^ 2 := by
    field_simp
    ring
  rw [hval] at ht
  have hc2 : 0 < c ^ 2 := by positivity
  have hnum : 0 < c ^ 2 * (2 - d) := by nlinarith
  have hden : 0 < (1 - d) ^ 2 := by positivity
  have : 0 < c ^ 2 * (2 - d) / (1 - d) ^ 2 := div_pos hnum hden
  linarith

/-- **Cauchy–Schwarz kernel property**: for a negative semi-definite symmetric form, a vector of zero
square in the span is orthogonal to the whole span. The proof is the discriminant trick above, with
no analysis and no completeness. -/
theorem pairing_eq_zero_of_self_eq_zero {B : BilinForm K M} {S : Set M} (hsymm : B.IsSymm)
    (hneg : NegSemidefiniteOn B S) {x : M} (hx : x ∈ Submodule.span K S) (hx0 : B x x = 0)
    {w : M} (hw : w ∈ Submodule.span K S) : B x w = 0 := by
  have hexp : ∀ t : K, B (x + t • w) (x + t • w) = 2 * t * B x w + t ^ 2 * B w w := by
    intro t
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hx0,
      hsymm.eq w x]
    ring
  refine eq_zero_of_quadratic_nonpos (hneg w hw) fun t => ?_
  rw [← hexp t]
  exact hneg _ (Submodule.add_mem _ hx (Submodule.smul_mem _ t hw))

/-- **The core**: a symmetric form that is negative semi-definite and non-degenerate on the span of
`S` is negative definite there. -/
theorem negDefinite_of_semidefiniteOn_of_nondegenerateOn {B : BilinForm K M} {S : Set M}
    (hsymm : B.IsSymm) (hneg : NegSemidefiniteOn B S) (hnd : NondegenerateOn B S)
    {x : M} (hx : x ∈ Submodule.span K S) (hx0 : x ≠ 0) : B x x < 0 := by
  rcases lt_or_eq_of_le (hneg x hx) with h | h
  · exact h
  · exfalso
    obtain ⟨w, hw, hxw⟩ := hnd x hx hx0
    exact hxw (pairing_eq_zero_of_self_eq_zero hsymm hneg hx h hw)

/-! ### Why orthogonality to a non-negative-square vector is not enough -/

/-- **The shorter hypothesis fails.** On `K²` with the identity form — symmetric and non-degenerate —
the vector `h = (1, 0)` has `B h h = 1 ≥ 0` and is orthogonal to `e = (0, 1)`, yet `B e e = 1 > 0`, so
the form is *positive* definite on `{e}`. Hence "some vector of non-negative square orthogonal to the
family, plus non-degeneracy" does not give negative definiteness on the family: the missing input is
the signature condition, supplied here as `NegSemidefiniteOn`. -/
theorem not_negDefinite_of_orthogonal_nonneg_square :
    ∃ (B : BilinForm K (K × K)) (h e : K × K),
      B.IsSymm ∧ 0 ≤ B h h ∧ B h e = 0 ∧ e ≠ 0 ∧ 0 < B e e := by
  classical
  refine ⟨(LinearMap.mul K K).compl₁₂ (LinearMap.fst K K K) (LinearMap.fst K K K) +
      (LinearMap.mul K K).compl₁₂ (LinearMap.snd K K K) (LinearMap.snd K K K),
    (1, 0), (0, 1), ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp [LinearMap.compl₁₂_apply, mul_comm]
  · simp [LinearMap.compl₁₂_apply]
  · simp [LinearMap.compl₁₂_apply]
  · simp
  · simp [LinearMap.compl₁₂_apply]

end KltDP.Support.NegativeDefinite
