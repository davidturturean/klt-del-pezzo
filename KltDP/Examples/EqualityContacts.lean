import Mathlib.Tactic

/-!
# Integral equality contacts

The finite arithmetic in the completeness argument of Proposition A.1 of the
frozen manuscript (lines 3217–3260). Contacts are arbitrary natural numbers;
the two intersection identities and integrality are the only restrictions.

This module does not construct a surface, a curve, or an intersection pairing.
The geometric application must prove these identities for actual curves and
realize every resulting integral class independently.
-/

namespace KltDP.EqualityContacts

/-- Contacts with one isolated higher-weight curve and its indexed `A₂` branch. -/
structure Branch where
  z : ℕ
  u : ℕ
  v : ℕ
  deriving DecidableEq, Repr

/-- The integral quadratic form of one `A₂` contact pair. -/
def Branch.q (b : Branch) : ℕ := b.u ^ 2 + b.u * b.v + b.v ^ 2

/-- Contacts with the four `[3]` blocks and three `A₂` blocks.

The three branch fields are labeled by `0, 1, ∞`, in that order. The natural
number `r` is three times the anticanonical degree, once a geometric adapter
has supplied this interpretation. No restriction is built into the type.
-/
structure Contact where
  r : ℕ
  zB : ℕ
  b0 : Branch
  b1 : Branch
  bInf : Branch
  deriving DecidableEq, Repr

/-- The source contact equations and all three integral-class congruences.

The congruence is written without truncated natural-number subtraction.
`closure_numerators_integral_iff` below proves its equivalence to integrality
of all three rational exceptional coefficients.
-/
def Contact.Admissible (c : Contact) : Prop :=
  0 < c.r ∧
  c.r + c.zB + c.b0.z + c.b1.z + c.bInf.z = 3 ∧
  c.zB ^ 2 + c.b0.z ^ 2 + c.b1.z ^ 2 + c.bInf.z ^ 2 +
      2 * (c.b0.q + c.b1.q + c.bInf.q) = 3 + c.r ^ 2 ∧
  (c.zB + c.b0.z + c.b0.u + 2 * c.b0.v) % 3 = c.r % 3 ∧
  (c.zB + c.b1.z + c.b1.u + 2 * c.b1.v) % 3 = c.r % 3 ∧
  (c.zB + c.bInf.z + c.bInf.u + 2 * c.bInf.v) % 3 = c.r % 3

instance (c : Contact) : Decidable c.Admissible := by
  unfold Contact.Admissible
  infer_instance

/-- An integer numerator divided by three is integral exactly when divisible by three. -/
theorem third_integral_iff_three_dvd (n : ℤ) :
    (∃ k : ℤ, (n : ℚ) / 3 = (k : ℚ)) ↔ (3 : ℤ) ∣ n := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h : (n : ℚ) = 3 * (k : ℚ) := by linarith
    exact_mod_cast h
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    ring

/-- The single branch congruence is equivalent to divisibility of every closure numerator. -/
theorem closure_numerators_dvd_iff (r z0 zi u v : ℕ) :
    ((3 : ℤ) ∣ -(r : ℤ) + (z0 : ℤ) + (zi : ℤ) - 2 * (u : ℤ) - (v : ℤ)) ∧
      ((3 : ℤ) ∣ -(r : ℤ) + (z0 : ℤ) + (zi : ℤ) + (u : ℤ) - (v : ℤ)) ∧
      ((3 : ℤ) ∣ -(r : ℤ) + (z0 : ℤ) + (zi : ℤ) + (u : ℤ) + 2 * (v : ℤ)) ↔
      (z0 + zi + u + 2 * v) % 3 = r % 3 := by
  simp only [Int.dvd_iff_emod_eq_zero]
  constructor
  · rintro ⟨h1, h2, h3⟩
    omega
  · intro h
    refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Integrality of all three displayed exceptional coefficients, with integer
numerators and rational division, is equivalent to the branch congruence. -/
theorem closure_numerators_integral_iff (r z0 zi u v : ℕ) :
    (∃ k : ℤ,
      (((-(r : ℤ) + z0 + zi - 2 * u - v : ℤ) : ℚ) / 3) = (k : ℚ)) ∧
    (∃ k : ℤ,
      (((-(r : ℤ) + z0 + zi + u - v : ℤ) : ℚ) / 3) = (k : ℚ)) ∧
    (∃ k : ℤ,
      (((-(r : ℤ) + z0 + zi + u + 2 * v : ℤ) : ℚ) / 3) = (k : ℚ)) ↔
      (z0 + zi + u + 2 * v) % 3 = r % 3 := by
  simp_rw [third_integral_iff_three_dvd]
  exact closure_numerators_dvd_iff r z0 zi u v

/-- Positivity and the discrepancy-sum identity bound the degree numerator. -/
theorem degree_cases (c : Contact) (h : c.Admissible) :
    c.r = 1 ∨ c.r = 2 ∨ c.r = 3 := by
  rcases h with ⟨hr, hs, _⟩
  omega

/-- All higher-weight contacts are at most two. -/
theorem higher_contact_bounds (c : Contact) (h : c.Admissible) :
    c.zB ≤ 2 ∧ c.b0.z ≤ 2 ∧ c.b1.z ≤ 2 ∧ c.bInf.z ≤ 2 := by
  rcases h with ⟨hr, hs, _⟩
  omega

/-- The quadratic identity bounds each `A₂` branch form by six. -/
theorem branch_quadratic_bounds (c : Contact) (h : c.Admissible) :
    c.b0.q ≤ 6 ∧ c.b1.q ≤ 6 ∧ c.bInf.q ≤ 6 := by
  have hr := degree_cases c h
  rcases h with ⟨_, _, hq, _⟩
  rcases hr with hr | hr | hr <;> rw [hr] at hq <;> norm_num at hq <;> omega

/-- Coordinate bounds are proved before any finite enumeration is performed. -/
theorem Branch.coordinate_bounds (b : Branch) (h : b.q ≤ 6) :
    b.u ≤ 2 ∧ b.v ≤ 2 := by
  unfold Branch.q at h
  constructor <;> nlinarith

/-- The two weight-two coordinates are binary when the branch form is at most three. -/
theorem Branch.binary_bounds (b : Branch) (h : b.q ≤ 3) :
    b.u ≤ 1 ∧ b.v ≤ 1 := by
  unfold Branch.q at h
  constructor <;> nlinarith

/-- For degree one and zero contact with `B`, these are all branch possibilities. -/
theorem branch_one_zero (b : Branch) (hz : b.z ≤ 2) (hq : b.q ≤ 2)
    (hm : (b.z + b.u + 2 * b.v) % 3 = 1) :
    b = ⟨0, 1, 0⟩ ∨ b = ⟨1, 0, 0⟩ ∨ b = ⟨2, 0, 1⟩ := by
  have hb := b.binary_bounds (by omega)
  rcases b with ⟨z, u, v⟩
  rcases hb with ⟨hu, hv⟩
  simp only [Branch.q] at hq
  interval_cases z <;> interval_cases u <;> interval_cases v <;> norm_num at *

/-- For degree one and contact one with `B`, these are all branch possibilities. -/
theorem branch_one_one (b : Branch) (hz : b.z ≤ 1) (hq : b.q ≤ 2)
    (hm : (1 + b.z + b.u + 2 * b.v) % 3 = 1) :
    b = ⟨0, 0, 0⟩ ∨ b = ⟨1, 0, 1⟩ := by
  have hb := b.binary_bounds (by omega)
  rcases b with ⟨z, u, v⟩
  rcases hb with ⟨hu, hv⟩
  simp only [Branch.q] at hq
  interval_cases z <;> interval_cases u <;> interval_cases v <;> norm_num at *

/-- Contact two with `B` forces a nonzero branch form at every branch. -/
theorem branch_one_two (b : Branch) (hz : b.z = 0) (hq : b.q ≤ 2)
    (hm : (2 + b.z + b.u + 2 * b.v) % 3 = 1) :
    b = ⟨0, 0, 1⟩ := by
  have hb := b.binary_bounds (by omega)
  rcases b with ⟨z, u, v⟩
  rcases hb with ⟨hu, hv⟩
  simp only [Branch.q] at hq
  change z = 0 at hz
  subst z
  interval_cases u <;> interval_cases v <;> norm_num at *

/-- For degree two and zero contact with `B`, the branch is determined by `z`. -/
theorem branch_two_zero (b : Branch) (hz : b.z ≤ 1) (hq : b.q ≤ 3)
    (hm : (b.z + b.u + 2 * b.v) % 3 = 2) :
    b = ⟨0, 0, 1⟩ ∨ b = ⟨1, 1, 0⟩ := by
  have hb := b.binary_bounds hq
  rcases b with ⟨z, u, v⟩
  rcases hb with ⟨hu, hv⟩
  simp only [Branch.q] at hq
  interval_cases z <;> interval_cases u <;> interval_cases v <;> norm_num at *

/-- For degree two and contact one with `B`, every branch is the same. -/
theorem branch_two_one (b : Branch) (hz : b.z = 0) (hq : b.q ≤ 3)
    (hm : (1 + b.z + b.u + 2 * b.v) % 3 = 2) :
    b = ⟨0, 1, 0⟩ := by
  have hb := b.binary_bounds hq
  rcases b with ⟨z, u, v⟩
  rcases hb with ⟨hu, hv⟩
  simp only [Branch.q] at hq
  change z = 0 at hz
  subst z
  interval_cases u <;> interval_cases v <;> norm_num at *

/-- Degree-three integrality forces equal binary contacts at each `A₂` branch. -/
theorem branch_three (b : Branch) (hz : b.z = 0) (hq : b.q ≤ 6)
    (hm : (b.z + b.u + 2 * b.v) % 3 = 0) :
    b = ⟨0, 0, 0⟩ ∨ b = ⟨0, 1, 1⟩ := by
  have hb := b.coordinate_bounds hq
  rcases b with ⟨z, u, v⟩
  rcases hb with ⟨hu, hv⟩
  simp only [Branch.q] at hq
  change z = 0 at hz
  subst z
  interval_cases u <;> interval_cases v <;> norm_num at *

/-- The contact pattern called `Pᵢ` in the manuscript. -/
def P (i : Fin 3) : Contact :=
  ⟨1, 1, if i = 0 then ⟨1, 0, 1⟩ else ⟨0, 0, 0⟩,
    if i = 1 then ⟨1, 0, 1⟩ else ⟨0, 0, 0⟩,
    if i = 2 then ⟨1, 0, 1⟩ else ⟨0, 0, 0⟩⟩

/-- The contact pattern called `Tᵢ` in the manuscript. -/
def T (i : Fin 3) : Contact :=
  ⟨1, 0, if i = 0 then ⟨0, 1, 0⟩ else ⟨1, 0, 0⟩,
    if i = 1 then ⟨0, 1, 0⟩ else ⟨1, 0, 0⟩,
    if i = 2 then ⟨0, 1, 0⟩ else ⟨1, 0, 0⟩⟩

/-- The contact pattern called `Θ` in the manuscript. -/
def theta : Contact := ⟨2, 1, ⟨0, 1, 0⟩, ⟨0, 1, 0⟩, ⟨0, 1, 0⟩⟩

/-- The contact pattern called `Qᵢ` in the manuscript. -/
def Q (i : Fin 3) : Contact :=
  ⟨2, 0, if i = 0 then ⟨1, 1, 0⟩ else ⟨0, 0, 1⟩,
    if i = 1 then ⟨1, 1, 0⟩ else ⟨0, 0, 1⟩,
    if i = 2 then ⟨1, 1, 0⟩ else ⟨0, 0, 1⟩⟩

/-- The contact pattern called `Wᵢ` in the manuscript; branch `i` is untouched. -/
def W (i : Fin 3) : Contact :=
  ⟨3, 0, if i = 0 then ⟨0, 0, 0⟩ else ⟨0, 1, 1⟩,
    if i = 1 then ⟨0, 0, 0⟩ else ⟨0, 1, 1⟩,
    if i = 2 then ⟨0, 0, 0⟩ else ⟨0, 1, 1⟩⟩

/-- A list of candidate patterns, separately from the equation-based predicate. -/
def patterns : Finset Contact :=
  {P 0, P 1, P 2, T 0, T 1, T 2, theta, Q 0, Q 1, Q 2, W 0, W 1, W 2}

set_option maxHeartbeats 2000000 in
/-- Completeness: every nonnegative integral solution is one of the thirteen patterns.

The proof first bounds the degree and local coordinates, then combines at most
three local branch choices. It does not search an assumed bound on all inputs.
The scoped heartbeat budget covers the kernel-checked finite cases; impossible
cases are eliminated from the two identities before reducing list membership.
-/
theorem mem_patterns_of_admissible (c : Contact) (h : c.Admissible) :
    c ∈ patterns := by
  have hr := degree_cases c h
  rcases c with ⟨r, zB, b0, b1, bInf⟩
  rcases h with ⟨hp, hs, hq, hm0, hm1, hmInf⟩
  change r = 1 ∨ r = 2 ∨ r = 3 at hr
  dsimp only at hp hs hq hm0 hm1 hmInf
  rcases hr with rfl | rfl | rfl
  · have hb0 : b0.q ≤ 2 := by omega
    have hb1 : b1.q ≤ 2 := by omega
    have hbInf : bInf.q ≤ 2 := by omega
    have hzB : zB ≤ 2 := by omega
    interval_cases zB
    · have hc0 := branch_one_zero b0 (by omega) hb0 (by simpa using hm0)
      have hc1 := branch_one_zero b1 (by omega) hb1 (by simpa using hm1)
      have hcInf := branch_one_zero bInf (by omega) hbInf (by simpa using hmInf)
      rcases hc0 with rfl | rfl | rfl <;>
        rcases hc1 with rfl | rfl | rfl <;>
        rcases hcInf with rfl | rfl | rfl <;>
        norm_num [Branch.q] at hs hq <;> decide
    · have hc0 := branch_one_one b0 (by omega) hb0 (by simpa using hm0)
      have hc1 := branch_one_one b1 (by omega) hb1 (by simpa using hm1)
      have hcInf := branch_one_one bInf (by omega) hbInf (by simpa using hmInf)
      rcases hc0 with rfl | rfl <;>
        rcases hc1 with rfl | rfl <;>
        rcases hcInf with rfl | rfl <;>
        norm_num [Branch.q] at hs hq <;> decide
    · have hc0 := branch_one_two b0 (by omega) hb0 (by simpa using hm0)
      have hc1 := branch_one_two b1 (by omega) hb1 (by simpa using hm1)
      have hcInf := branch_one_two bInf (by omega) hbInf (by simpa using hmInf)
      subst b0 b1 bInf
      norm_num [Branch.q] at hq
  · have hb0 : b0.q ≤ 3 := by omega
    have hb1 : b1.q ≤ 3 := by omega
    have hbInf : bInf.q ≤ 3 := by omega
    have hzB : zB ≤ 1 := by omega
    interval_cases zB
    · have hc0 := branch_two_zero b0 (by omega) hb0 (by simpa using hm0)
      have hc1 := branch_two_zero b1 (by omega) hb1 (by simpa using hm1)
      have hcInf := branch_two_zero bInf (by omega) hbInf (by simpa using hmInf)
      rcases hc0 with rfl | rfl <;>
        rcases hc1 with rfl | rfl <;>
        rcases hcInf with rfl | rfl <;>
        norm_num [Branch.q] at hs hq <;> decide
    · have hc0 := branch_two_one b0 (by omega) hb0 (by simpa using hm0)
      have hc1 := branch_two_one b1 (by omega) hb1 (by simpa using hm1)
      have hcInf := branch_two_one bInf (by omega) hbInf (by simpa using hmInf)
      subst b0 b1 bInf
      decide
  · have hzB : zB = 0 := by omega
    subst zB
    have hb0 : b0.q ≤ 6 := by omega
    have hb1 : b1.q ≤ 6 := by omega
    have hbInf : bInf.q ≤ 6 := by omega
    have hc0 := branch_three b0 (by omega) hb0 (by simpa using hm0)
    have hc1 := branch_three b1 (by omega) hb1 (by simpa using hm1)
    have hcInf := branch_three bInf (by omega) hbInf (by simpa using hmInf)
    rcases hc0 with rfl | rfl <;>
      rcases hc1 with rfl | rfl <;>
      rcases hcInf with rfl | rfl <;>
      norm_num [Branch.q] at hs hq <;> decide

/-- Every displayed pattern satisfies the exact equations and integral congruences. -/
theorem admissible_of_mem_patterns (c : Contact) (h : c ∈ patterns) :
    c.Admissible := by
  simp only [patterns, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Exact arithmetic classification, in both directions. -/
theorem admissible_iff_mem_patterns (c : Contact) :
    c.Admissible ↔ c ∈ patterns :=
  ⟨mem_patterns_of_admissible c, admissible_of_mem_patterns c⟩

/-- There are thirteen distinct integral solutions of the contact equations. -/
theorem patterns_card : patterns.card = 13 := by decide

/-- Exactly six solutions have degree numerator one. -/
theorem degree_one_card : (patterns.filter (fun c => c.r = 1)).card = 6 := by decide

/-- Exactly four solutions have degree numerator two. -/
theorem degree_two_card : (patterns.filter (fun c => c.r = 2)).card = 4 := by decide

/-- Exactly three solutions have degree numerator three. -/
theorem degree_three_card : (patterns.filter (fun c => c.r = 3)).card = 3 := by decide

end KltDP.EqualityContacts
