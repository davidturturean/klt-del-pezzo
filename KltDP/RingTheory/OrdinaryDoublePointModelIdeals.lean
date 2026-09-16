import KltDP.RingTheory.OrdinaryDoublePointModelCotangent
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# The fibre-product ideal theory of `k⟦x, y⟧ ⧸ (x y)`

BRIEF27, item (G1). The model `M = k⟦x, y⟧ ⧸ (x y)` embeds into `k⟦x⟧ × k⟦y⟧` by restricting a series
to the two axes: `ev i : k⟦x, y⟧ →+* k⟦X⟧` keeps the coefficients of the powers of `X i` alone
(`coeff_ev`; multiplicativity from `MvPowerSeries.coeff_mul` and `Finsupp.antidiagonal_single`).

* `ev_zero_eq_zero_iff : ev 0 φ = 0 ↔ X 1 ∣ φ`, `ev_one_eq_zero_iff : ev 1 φ = 0 ↔ X 0 ∣ φ`;
  `mem_nodeIdeal_iff : φ ∈ (X 0 · X 1) ↔ ev 0 φ = 0 ∧ ev 1 φ = 0` — the kernel of `(ev 0, ev 1)` is `(x y)`.
* On the model: `evM i : M →+* k⟦X⟧`, `eq_zero_iff_evM : z = 0 ↔ evM 0 z = 0 ∧ evM 1 z = 0`,
  `mem_span_xBar_zero_iff : z ∈ (x̄) ↔ evM 1 z = 0`, `mem_span_xBar_one_iff : z ∈ (ȳ) ↔ evM 0 z = 0`.
* **`branches_of_mul_eq_bot`**: ideals `A, B` of the model with `A · B = ⊥`, `A ≠ ⊥`, `B ≠ ⊥` satisfy
  `A ≤ (x̄) ∧ B ≤ (ȳ)` or `A ≤ (ȳ) ∧ B ≤ (x̄)` (`k⟦X⟧` is a domain); `le_span_of_mul_eq_bot` is the
  one-sided form needing only `B ≠ ⊥`.
* `xBar_not_mem_sq : x̄, ȳ ∉ m_M ^ 2`, `mul_eq_zero_of_mem_span_xBar : a ∈ (x̄) → b ∈ (ȳ) → a b = 0`.
-/

noncomputable section

open IsLocalRing

universe u

namespace KltDP.RingTheory.OrdinaryDoublePointModel

open KltDP.Geometry.IntrinsicNodal

variable (k : Type u) [Field k]

/-! ## Restriction to the axes -/

/-- Restriction of a two-variable series to the `X i`-axis: the one-variable series whose `n`-th
coefficient is the coefficient of `X i ^ n`. -/
def ev (i : Fin 2) : PS k →+* PowerSeries k where
  toFun φ := PowerSeries.mk fun n => MvPowerSeries.coeff k (Finsupp.single i n) φ
  map_one' := by
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_mk, MvPowerSeries.coeff_one, PowerSeries.coeff_one]
    simp only [Finsupp.single_eq_zero]
  map_mul' φ ψ := by
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, MvPowerSeries.coeff_mul,
      Finsupp.antidiagonal_single, Finset.sum_map]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_fst,
      Prod.map_snd, PowerSeries.coeff_mk]
  map_zero' := by
    refine PowerSeries.ext fun n => ?_
    simp only [PowerSeries.coeff_mk, map_zero]
  map_add' φ ψ := by
    refine PowerSeries.ext fun n => ?_
    simp only [PowerSeries.coeff_mk, map_add]

theorem coeff_ev (i : Fin 2) (φ : PS k) (n : ℕ) :
    PowerSeries.coeff k n (ev k i φ) = MvPowerSeries.coeff k (Finsupp.single i n) φ := by
  show PowerSeries.coeff k n (PowerSeries.mk fun m => MvPowerSeries.coeff k (Finsupp.single i m) φ) = _
  exact PowerSeries.coeff_mk _ _

theorem ev_zero_eq_zero_iff (φ : PS k) : ev k 0 φ = 0 ↔ (MvPowerSeries.X 1 : PS k) ∣ φ := by
  rw [MvPowerSeries.X_dvd_iff]
  constructor
  · intro h m hm
    have hm' : m = Finsupp.single 0 (m 0) := Finsupp.ext fun l => by
      fin_cases l
      · simp
      · simpa using hm
    rw [hm', ← coeff_ev, h, map_zero]
  · intro h
    refine PowerSeries.ext fun n => ?_
    rw [coeff_ev, map_zero]
    exact h _ (by simp)

theorem ev_one_eq_zero_iff (φ : PS k) : ev k 1 φ = 0 ↔ (MvPowerSeries.X 0 : PS k) ∣ φ := by
  rw [MvPowerSeries.X_dvd_iff]
  constructor
  · intro h m hm
    have hm' : m = Finsupp.single 1 (m 1) := Finsupp.ext fun l => by
      fin_cases l
      · simpa using hm
      · simp
    rw [hm', ← coeff_ev, h, map_zero]
  · intro h
    refine PowerSeries.ext fun n => ?_
    rw [coeff_ev, map_zero]
    exact h _ (by simp)

theorem ev_zero_X_one : ev k 0 (MvPowerSeries.X 1 : PS k) = 0 :=
  (ev_zero_eq_zero_iff k _).mpr dvd_rfl

theorem ev_one_X_zero : ev k 1 (MvPowerSeries.X 0 : PS k) = 0 :=
  (ev_one_eq_zero_iff k _).mpr dvd_rfl

/-- **The kernel of `(ev 0, ev 1)` is `(X 0 · X 1)`.** -/
theorem mem_nodeIdeal_iff (φ : PS k) : φ ∈ nodeIdeal k ↔ ev k 0 φ = 0 ∧ ev k 1 φ = 0 := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨ψ, rfl⟩
    constructor
    · rw [map_mul, map_mul, ev_zero_X_one, mul_zero, zero_mul]
    · rw [map_mul, map_mul, ev_one_X_zero, zero_mul, zero_mul]
  · rintro ⟨h0, h1⟩
    obtain ⟨φ', rfl⟩ := (ev_one_eq_zero_iff k φ).mp h1
    refine mul_dvd_mul_left _ ?_
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    have h := MvPowerSeries.coeff_add_monomial_mul (m := Finsupp.single 0 1) (n := m) (φ := φ')
      (1 : k)
    rw [one_mul] at h
    rw [← h, ← MvPowerSeries.X]
    have h0' := (ev_zero_eq_zero_iff k _).mp h0
    rw [MvPowerSeries.X_dvd_iff] at h0'
    exact h0' _ (by rw [Finsupp.add_apply, hm, Finsupp.single_eq_of_ne (by decide), add_zero])

/-! ## The model as a subring of `k⟦x⟧ × k⟦y⟧` -/

/-- Restriction of the model to the `x̄`-axis (`i = 0`) or the `ȳ`-axis (`i = 1`). -/
def evM (i : Fin 2) : ordinaryDoublePointModel k →+* PowerSeries k :=
  Ideal.Quotient.lift (nodeIdeal k) (ev k i) fun φ hφ => by
    obtain ⟨h0, h1⟩ := (mem_nodeIdeal_iff k φ).mp hφ
    fin_cases i
    · exact h0
    · exact h1

theorem evM_mk (i : Fin 2) (φ : PS k) :
    evM k i (Ideal.Quotient.mk (nodeIdeal k) φ) = ev k i φ :=
  Ideal.Quotient.lift_mk _ _ _

/-- An element of the model vanishes iff both axis restrictions vanish. -/
theorem eq_zero_iff_evM (z : ordinaryDoublePointModel k) :
    z = 0 ↔ evM k 0 z = 0 ∧ evM k 1 z = 0 := by
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_nodeIdeal_iff, evM_mk, evM_mk]

theorem mem_span_xBar_zero_iff (z : ordinaryDoublePointModel k) :
    z ∈ Ideal.span {(xBar k 0 : ordinaryDoublePointModel k)} ↔ evM k 1 z = 0 := by
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [evM_mk, ev_one_eq_zero_iff, xBar_val, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨ψ, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← map_mul, Ideal.Quotient.eq] at ha
    have h1 : (MvPowerSeries.X 0 : PS k) ∣ φ - MvPowerSeries.X 0 * ψ :=
      dvd_trans (dvd_mul_right _ _) (Ideal.mem_span_singleton.mp ha)
    have h2 := dvd_add h1 (dvd_mul_right (MvPowerSeries.X 0 : PS k) ψ)
    rwa [sub_add_cancel] at h2
  · rintro ⟨ψ, rfl⟩
    exact ⟨Ideal.Quotient.mk (nodeIdeal k) ψ, by rw [← map_mul]⟩

theorem mem_span_xBar_one_iff (z : ordinaryDoublePointModel k) :
    z ∈ Ideal.span {(xBar k 1 : ordinaryDoublePointModel k)} ↔ evM k 0 z = 0 := by
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [evM_mk, ev_zero_eq_zero_iff, xBar_val, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨ψ, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← map_mul, Ideal.Quotient.eq] at ha
    have h1 : (MvPowerSeries.X 1 : PS k) ∣ φ - MvPowerSeries.X 1 * ψ :=
      dvd_trans (dvd_mul_left _ _) (Ideal.mem_span_singleton.mp ha)
    have h2 := dvd_add h1 (dvd_mul_right (MvPowerSeries.X 1 : PS k) ψ)
    rwa [sub_add_cancel] at h2
  · rintro ⟨ψ, rfl⟩
    exact ⟨Ideal.Quotient.mk (nodeIdeal k) ψ, by rw [← map_mul]⟩

/-! ## Ideals with zero product lie on the two branches -/

theorem mul_eq_zero_of_mul_eq_bot {A B : Ideal (ordinaryDoublePointModel k)} (h : A * B = ⊥)
    {a b : ordinaryDoublePointModel k} (ha : a ∈ A) (hb : b ∈ B) : a * b = 0 :=
  Ideal.mem_bot.mp (h ▸ Ideal.mul_mem_mul ha hb)

/-- One-sided form: if `A · B = 0` and `B ≠ 0`, then `A` lies on one of the two branches. -/
theorem le_span_of_mul_eq_bot {A B : Ideal (ordinaryDoublePointModel k)} (h : A * B = ⊥)
    (hB : B ≠ ⊥) :
    A ≤ Ideal.span {(xBar k 0 : ordinaryDoublePointModel k)} ∨
      A ≤ Ideal.span {(xBar k 1 : ordinaryDoublePointModel k)} := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
  have hb' : ¬ (evM k 0 b = 0 ∧ evM k 1 b = 0) := fun h' => hb0 ((eq_zero_iff_evM k b).mpr h')
  rw [not_and_or] at hb'
  rcases hb' with h0 | h1
  · right
    intro a ha
    rw [mem_span_xBar_one_iff]
    have h2 := congrArg (evM k 0) (mul_eq_zero_of_mul_eq_bot k h ha hb)
    rw [map_mul, map_zero] at h2
    exact (mul_eq_zero.mp h2).resolve_right h0
  · left
    intro a ha
    rw [mem_span_xBar_zero_iff]
    have h2 := congrArg (evM k 1) (mul_eq_zero_of_mul_eq_bot k h ha hb)
    rw [map_mul, map_zero] at h2
    exact (mul_eq_zero.mp h2).resolve_right h1

/-- Two nonzero ideals on the same branch have a nonzero product. -/
theorem mul_ne_bot_of_le_span {A B : Ideal (ordinaryDoublePointModel k)} (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (i : Fin 2) (hAi : A ≤ Ideal.span {(xBar k i : ordinaryDoublePointModel k)})
    (hBi : B ≤ Ideal.span {(xBar k i : ordinaryDoublePointModel k)}) : A * B ≠ ⊥ := by
  intro h
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
  have hab := mul_eq_zero_of_mul_eq_bot k h ha hb
  fin_cases i
  · have ha1 : evM k 1 a = 0 := (mem_span_xBar_zero_iff k a).mp (hAi ha)
    have hb1 : evM k 1 b = 0 := (mem_span_xBar_zero_iff k b).mp (hBi hb)
    have ha0' : evM k 0 a ≠ 0 := fun h' => ha0 ((eq_zero_iff_evM k a).mpr ⟨h', ha1⟩)
    have hb0' : evM k 0 b ≠ 0 := fun h' => hb0 ((eq_zero_iff_evM k b).mpr ⟨h', hb1⟩)
    have h2 := congrArg (evM k 0) hab
    rw [map_mul, map_zero] at h2
    exact mul_ne_zero ha0' hb0' h2
  · have ha1 : evM k 0 a = 0 := (mem_span_xBar_one_iff k a).mp (hAi ha)
    have hb1 : evM k 0 b = 0 := (mem_span_xBar_one_iff k b).mp (hBi hb)
    have ha0' : evM k 1 a ≠ 0 := fun h' => ha0 ((eq_zero_iff_evM k a).mpr ⟨ha1, h'⟩)
    have hb0' : evM k 1 b ≠ 0 := fun h' => hb0 ((eq_zero_iff_evM k b).mpr ⟨hb1, h'⟩)
    have h2 := congrArg (evM k 1) hab
    rw [map_mul, map_zero] at h2
    exact mul_ne_zero ha0' hb0' h2

/-- **Nonzero ideals of the model with zero product lie on the two different branches.** -/
theorem branches_of_mul_eq_bot {A B : Ideal (ordinaryDoublePointModel k)} (h : A * B = ⊥)
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) :
    (A ≤ Ideal.span {(xBar k 0 : ordinaryDoublePointModel k)} ∧
        B ≤ Ideal.span {(xBar k 1 : ordinaryDoublePointModel k)}) ∨
      (A ≤ Ideal.span {(xBar k 1 : ordinaryDoublePointModel k)} ∧
        B ≤ Ideal.span {(xBar k 0 : ordinaryDoublePointModel k)}) := by
  have hBA : B * A = ⊥ := by rw [mul_comm B A]; exact h
  rcases le_span_of_mul_eq_bot k h hB with hA0 | hA1
  · left
    refine ⟨hA0, ?_⟩
    rcases le_span_of_mul_eq_bot k hBA hA with hB0 | hB1
    · exact absurd h (mul_ne_bot_of_le_span k hA hB 0 hA0 hB0)
    · exact hB1
  · right
    refine ⟨hA1, ?_⟩
    rcases le_span_of_mul_eq_bot k hBA hA with hB0 | hB1
    · exact hB0
    · exact absurd h (mul_ne_bot_of_le_span k hA hB 1 hA1 hB1)

/-! ## Two more facts about the branches -/

/-- `x̄`, `ȳ` are not in `m_M ^ 2`. -/
theorem xBar_not_mem_sq (i : Fin 2) :
    (xBar k i : ordinaryDoublePointModel k) ∉ maximalIdeal (ordinaryDoublePointModel k) ^ 2 := by
  intro h
  exact (linearIndependent_xBar k).ne_zero i ((Ideal.toCotangent_eq_zero _ _).mpr h)

/-- The product of an element of `(x̄)` and an element of `(ȳ)` vanishes. -/
theorem mul_eq_zero_of_mem_span_xBar {a b : ordinaryDoublePointModel k}
    (ha : a ∈ Ideal.span {(xBar k 0 : ordinaryDoublePointModel k)})
    (hb : b ∈ Ideal.span {(xBar k 1 : ordinaryDoublePointModel k)}) : a * b = 0 := by
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  calc u * xBar k 0 * (v * xBar k 1) = u * v * (xBar k 0 * xBar k 1) := by ring
    _ = 0 := by rw [xBar_mul_xBar, mul_zero]

end KltDP.RingTheory.OrdinaryDoublePointModel
