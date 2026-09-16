import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Support obligation U-SINGLE-EFFECTIVE: numerical clauses of the single-adjoint configuration

Manuscript `source/manuscript.tex` lines 2416–2444 (proof of Theorem 8.1
`thm:adjoint-reduction`, the adjoint `N ∼ K_S + C + B₁ + B₂ + 2P`). Plan contract
(`U-SINGLE-EFFECTIVE`): construct `N ≥ 0`, show exterior coefficient mass one, exclude
`R = P`, prove `R` disjoint from the four core curves, `R² = K·R = −1`, and exceptional
remainder `Z = 0`.

Arithmetic clauses proved here, on the explicit core Gram matrix of `(C, B₁, B₂, P)` with
`C² = −2`, `B₁² = −3`, `B₂² = −β`, `P² = −1`, `C·P = B₁·P = B₂·P = 1`, all other products
zero, and `T = C + B₁ + B₂ + 2P`:

* `T² = 3 − β`;
* "Squaring `K_S ∼ R − T` gives `K_S² = 2 − β`": with `R² = −1` and `R·T = 0`,
  `(R − T)² = 2 − β`;
* "Rationality gives `#Irr(D) = β + 7`": `ρ = 10 − K² = 8 + β` and `#Irr(D) = ρ − 1`;
* "the forest count with at least eight components gives at most `β − 1` edges":
  `edges = vertices − components ≤ (β + 7) − 8`;
* "If `R = P`, the vanishing of `N` against each of `C, B₁, B₂` forces all three to occur
  in `Z`; then `Z·P ≥ 3`": a nonnegative combination containing `C, B₁, B₂` with
  coefficient at least one has `P`-degree at least three when every term is nonnegative.

Not proved here: effectivity of `N` (Riemann–Roch, `h⁰(−T) = 0`), the threshold bound on
the exterior coefficient mass, adjunction, negative definiteness of the exceptional
support and the contact formula for actual curves (F03, F05, F06, F20, Lemma 3.3).
-/

namespace KltDP.Support

open Matrix

/-- Gram matrix of `(C, B₁, B₂, P)` for the single-adjoint core with `B₂² = −β`. -/
def coreGram (β : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-2, 0, 0, 1; 0, -3, 0, 1; 0, 0, -β, 1; 1, 1, 1, -1]

/-- Coefficients of `T = C + B₁ + B₂ + 2P`. -/
def coreT : Fin 4 → ℤ := ![1, 1, 1, 2]

/-- `T² = 3 − β`. -/
theorem coreT_square (β : ℤ) : coreT ⬝ᵥ (coreGram β *ᵥ coreT) = 3 - β := by
  simp [coreGram, coreT, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- "Squaring `K_S ∼ R − T` gives `K_S² = 2 − β`": from `R² = −1`, `R·T = 0`, `T² = 3 − β`. -/
theorem canonical_square_of_adjoint (β RR RT TT : ℤ) (hR : RR = -1) (hRT : RT = 0)
    (hT : TT = 3 - β) : RR - 2 * RT + TT = 2 - β := by
  subst hR hRT hT; ring

/-- Noether's formula on a rational surface: `ρ = 10 − K²`, so `K² = 2 − β` gives `ρ = 8 + β`
and `#Irr(D) = ρ − 1 = β + 7`. -/
theorem picard_rank_and_component_count (β ρ K2 r : ℤ) (hNoether : K2 + ρ = 10)
    (hK : K2 = 2 - β) (hr : r = ρ - 1) : ρ = 8 + β ∧ r = β + 7 := by
  constructor <;> linarith

/-- The forest count: with at least eight components, `edges = vertices − components ≤ β − 1`. -/
theorem edges_le_of_components (β vertices edges components : ℤ)
    (hforest : edges + components = vertices) (hv : vertices = β + 7)
    (hc : 8 ≤ components) : edges ≤ β - 1 := by
  linarith

/-- "If `R = P`, ... all three [of `C, B₁, B₂`] occur in `Z`; then `Z·P ≥ 3`." -/
theorem Z_dot_P_ge_three {ι : Type*} (s : Finset ι) (z d : ι → ℤ)
    (hnonneg : ∀ i ∈ s, 0 ≤ z i * d i)
    (c b₁ b₂ : ι) (hc : c ∈ s) (hb₁ : b₁ ∈ s) (hb₂ : b₂ ∈ s)
    (hcb₁ : c ≠ b₁) (hcb₂ : c ≠ b₂) (hb₁b₂ : b₁ ≠ b₂)
    (hzc : 1 ≤ z c) (hzb₁ : 1 ≤ z b₁) (hzb₂ : 1 ≤ z b₂)
    (hdc : d c = 1) (hdb₁ : d b₁ = 1) (hdb₂ : d b₂ = 1) :
    3 ≤ ∑ i ∈ s, z i * d i := by
  classical
  have hsub : ({c, b₁, b₂} : Finset ι) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hle : ∑ i ∈ ({c, b₁, b₂} : Finset ι), z i * d i ≤ ∑ i ∈ s, z i * d i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hnonneg i hi)
  have hnotin : c ∉ ({b₁, b₂} : Finset ι) := by simp [hcb₁, hcb₂]
  rw [Finset.sum_insert hnotin, Finset.sum_pair hb₁b₂, hdc, hdb₁, hdb₂] at hle
  linarith

/-- **U-SINGLE-EFFECTIVE**, numerical clauses. -/
theorem u_single_effective_arithmetic :
    (∀ β : ℤ, coreT ⬝ᵥ (coreGram β *ᵥ coreT) = 3 - β) ∧
    (∀ β RR RT TT : ℤ, RR = -1 → RT = 0 → TT = 3 - β → RR - 2 * RT + TT = 2 - β) ∧
    (∀ β ρ K2 r : ℤ, K2 + ρ = 10 → K2 = 2 - β → r = ρ - 1 → ρ = 8 + β ∧ r = β + 7) ∧
    (∀ β vertices edges components : ℤ, edges + components = vertices → vertices = β + 7 →
      8 ≤ components → edges ≤ β - 1) :=
  ⟨coreT_square, canonical_square_of_adjoint, picard_rank_and_component_count,
    edges_le_of_components⟩

end KltDP.Support
