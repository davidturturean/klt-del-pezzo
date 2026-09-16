import KltDP.Examples.EqualityContacts

/-!
# Support obligation U-EQUALITY-CONTACT-CERT: thirteen contact rows and integral classes

Manuscript `source/manuscript.tex` lines 3221–3261 (completeness argument of
Proposition A.1). The accepted module `KltDP.Examples.EqualityContacts` proves
the finite classification of admissible contact data `(r, z_0, z_i, u_i, v_i)`:
`admissible_iff_mem_patterns` and `patterns_card = 13`. This module adds the
rank-one closure formulas that turn an admissible contact into an integral
class in the basis `a, b, E_{i1}, E_{i2}, E_{i3}`:

`[a] = r - z_0`, `[b] = r - 1`,
`[E_{i1}] = (-r + z_0 + z_i - 2u_i - v_i)/3`,
`[E_{i2}] = (-r + z_0 + z_i + u_i - v_i)/3`,
`[E_{i3}] = (-r + z_0 + z_i + u_i + 2v_i)/3`,

proves that every numerator of an admissible contact is divisible by three
(so the class is integral), that the thirteen resulting integral classes are
pairwise distinct, and that `r ∈ {1, 2, 3}`.

Not proved here (geometric clauses of the obligation): that an actual negative
exterior prime `Z` on `S_{3,3}` has contacts satisfying the two identities,
that the listed classes are realized by actual curves, and that two distinct
prime curves cannot share a negative class (F20, F34, Proposition A.1).
-/

namespace KltDP.Support

open KltDP.EqualityContacts

/-- The three `A₂` branches of a contact, indexed by `0, 1, ∞` as `Fin 3`. -/
def branchOf (c : Contact) : Fin 3 → Branch := ![c.b0, c.b1, c.bInf]

/-- Integer numerator of `[E_{i,j+1}]` for `j = 0, 1, 2`. -/
def closureNumerator (c : Contact) (i j : Fin 3) : ℤ :=
  let b := branchOf c i
  match j with
  | 0 => -(c.r : ℤ) + c.zB + b.z - 2 * b.u - b.v
  | 1 => -(c.r : ℤ) + c.zB + b.z + b.u - b.v
  | 2 => -(c.r : ℤ) + c.zB + b.z + b.u + 2 * b.v

/-- The rational closure coefficients `[E_{ij}]` of the manuscript. -/
def rationalE (c : Contact) (i j : Fin 3) : ℚ := (closureNumerator c i j : ℚ) / 3

/-- `[a] = r - z_0`. -/
def rationalA (c : Contact) : ℚ := (c.r : ℚ) - c.zB

/-- `[b] = r - 1`. -/
def rationalB (c : Contact) : ℚ := (c.r : ℚ) - 1

/-- An integral class in the basis `a, b, E_{i1}, E_{i2}, E_{i3}` (branches `0, 1, ∞`),
with explicit integer fields so that equality is structurally decidable. -/
structure ClassVector where
  a : ℤ
  b : ℤ
  e01 : ℤ
  e02 : ℤ
  e03 : ℤ
  e11 : ℤ
  e12 : ℤ
  e13 : ℤ
  eInf1 : ℤ
  eInf2 : ℤ
  eInf3 : ℤ
  deriving DecidableEq

/-- The `E_{i,j+1}` coefficient of a class vector. -/
def ClassVector.e (x : ClassVector) : Fin 3 → Fin 3 → ℤ :=
  ![![x.e01, x.e02, x.e03], ![x.e11, x.e12, x.e13], ![x.eInf1, x.eInf2, x.eInf3]]

/-- The integral class of a contact, with exact integer division of the numerators. -/
def integralClass (c : Contact) : ClassVector :=
  ⟨(c.r : ℤ) - c.zB, (c.r : ℤ) - 1,
    closureNumerator c 0 0 / 3, closureNumerator c 0 1 / 3, closureNumerator c 0 2 / 3,
    closureNumerator c 1 0 / 3, closureNumerator c 1 1 / 3, closureNumerator c 1 2 / 3,
    closureNumerator c 2 0 / 3, closureNumerator c 2 1 / 3, closureNumerator c 2 2 / 3⟩

theorem integralClass_e (c : Contact) (i j : Fin 3) :
    (integralClass c).e i j = closureNumerator c i j / 3 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem branch_congruence (c : Contact) (h : c.Admissible) (i : Fin 3) :
    (c.zB + (branchOf c i).z + (branchOf c i).u + 2 * (branchOf c i).v) % 3 = c.r % 3 := by
  obtain ⟨-, -, -, h0, h1, h2⟩ := h
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **Integrality.** Every closure numerator of an admissible contact is divisible by three. -/
theorem three_dvd_closureNumerator (c : Contact) (h : c.Admissible) (i j : Fin 3) :
    (3 : ℤ) ∣ closureNumerator c i j := by
  have hc := branch_congruence c h i
  have := (closure_numerators_dvd_iff c.r c.zB (branchOf c i).z (branchOf c i).u
    (branchOf c i).v).mpr hc
  obtain ⟨d0, d1, d2⟩ := this
  fin_cases j
  · simpa [closureNumerator] using d0
  · simpa [closureNumerator] using d1
  · simpa [closureNumerator] using d2

/-- The integral class agrees with the rational closure formulas. -/
theorem integralClass_e_cast (c : Contact) (h : c.Admissible) (i j : Fin 3) :
    ((integralClass c).e i j : ℚ) = rationalE c i j := by
  have hd := three_dvd_closureNumerator c h i j
  obtain ⟨k, hk⟩ := hd
  rw [integralClass_e, rationalE, hk, Int.mul_ediv_cancel_left k (by norm_num : (3 : ℤ) ≠ 0)]
  push_cast
  ring

theorem integralClass_a_cast (c : Contact) : ((integralClass c).a : ℚ) = rationalA c := by
  simp [integralClass, rationalA]

theorem integralClass_b_cast (c : Contact) : ((integralClass c).b : ℚ) = rationalB c := by
  simp [integralClass, rationalB]

/-- `r ∈ {1, 2, 3}` for every admissible contact. -/
theorem degree_one_two_three (c : Contact) (h : c.Admissible) :
    c.r = 1 ∨ c.r = 2 ∨ c.r = 3 :=
  degree_cases c h

/-- **Distinctness.** The thirteen patterns give thirteen distinct integral classes. -/
theorem integralClass_patterns_card : (patterns.image integralClass).card = 13 := by
  decide

/-- **U-EQUALITY-CONTACT-CERT**, arithmetic clause. -/
theorem u_equality_contact_cert :
    (∀ c : Contact, c.Admissible ↔ c ∈ patterns) ∧
    (∀ c : Contact, c.Admissible → c.r = 1 ∨ c.r = 2 ∨ c.r = 3) ∧
    (∀ c : Contact, c.Admissible → ∀ i j, (3 : ℤ) ∣ closureNumerator c i j) ∧
    (∀ c : Contact, c.Admissible → ∀ i j, ((integralClass c).e i j : ℚ) = rationalE c i j) ∧
    patterns.card = 13 ∧ (patterns.image integralClass).card = 13 :=
  ⟨admissible_iff_mem_patterns, degree_one_two_three, three_dvd_closureNumerator,
    integralClass_e_cast, patterns_card, integralClass_patterns_card⟩

end KltDP.Support
