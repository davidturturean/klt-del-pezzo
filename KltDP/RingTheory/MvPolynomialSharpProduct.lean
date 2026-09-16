import KltDP.RingTheory.MvPolynomialVarOrder
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Orders add sharply on a polynomial ring over a domain

BRIEF39, the one external input to the concrete domain instance. Over a domain, if `p` has order
exactly `a` at the origin and `q` order exactly `b`, then `p * q` has order exactly `a + b`:

  `p ∈ Iᵃ \ Iᵃ⁺¹`, `q ∈ Iᵇ \ Iᵇ⁺¹`  ⟹  `p * q ∉ Iᵃ⁺ᵇ⁺¹`,  where `I = varIdeal`.

## The argument

Write `P` and `Q` for the leading forms `homogeneousComponent a p` and `homogeneousComponent b q`.
They are nonzero exactly because `p ∉ Iᵃ⁺¹` (`homogeneousComponent_ne_zero_of_not_mem`), and
`p - P ∈ Iᵃ⁺¹`, `q - Q ∈ Iᵇ⁺¹` (`sub_homogeneousComponent_mem`). Expanding

  `p*q - P*Q = (p - P)*q + P*(q - Q)`

puts the difference in `Iᵃ⁺ᵇ⁺¹`, so if `p*q` were in `Iᵃ⁺ᵇ⁺¹` then so would be `P*Q`. But `P*Q` is
homogeneous of degree `a+b` and **nonzero** — this is the only place the domain hypothesis enters — and
a nonzero form of degree `d` is never in `Iᵈ⁺¹`, since it has a monomial of degree exactly `d`.

No graded ring, no direct sum and no initial-form ring homomorphism are needed: only the degree
filtration of `MvPolynomialVarOrder` and the fact that `MvPolynomial σ R` is a domain.
-/

noncomputable section

open MvPolynomial

universe u v

namespace KltDP.RingTheory.MvPolynomialSharpProduct

open KltDP.RingTheory.MvPolynomialVarOrder

variable {σ : Type u} {R : Type v} [CommRing R]

/-! ## Homogeneous polynomials and the filtration -/

/-- A form of degree `n` lies in the `n`-th power. -/
theorem homogeneous_mem_varIdeal_pow {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) : p ∈ varIdeal σ R ^ n := by
  refine degreeGE_le_varIdeal_pow n fun d hd => ?_
  by_contra hlt
  exact (MvPolynomial.mem_support_iff.mp hd) (hp.coeff_eq_zero (by omega))

/-- A **nonzero** form of degree `n` never lies one power deeper. -/
theorem homogeneous_not_mem_varIdeal_pow_succ {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) (hne : p ≠ 0) : p ∉ varIdeal σ R ^ (n + 1) := by
  intro hmem
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hne
  have hsupp : d ∈ p.support := MvPolynomial.mem_support_iff.mpr hd
  have hge : n + 1 ≤ d.degree := varIdeal_pow_le_degreeGE (n + 1) hmem d hsupp
  have heq : d.degree = n := by
    by_contra hne2
    exact hd (hp.coeff_eq_zero hne2)
  omega

/-! ## The leading form -/

/-- The leading form is nonzero exactly when the order is not larger. -/
theorem homogeneousComponent_ne_zero_of_not_mem {n : ℕ} {p : MvPolynomial σ R}
    (hmem : p ∈ varIdeal σ R ^ n) (hnot : p ∉ varIdeal σ R ^ (n + 1)) :
    homogeneousComponent n p ≠ 0 := by
  intro h0
  refine hnot (mem_pow_of_homogeneousComponent_eq_zero fun m hm => ?_)
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with h | h
  · exact homogeneousComponent_eq_zero_of_mem_pow hmem h
  · rw [h]; exact h0

/-- Subtracting the leading form moves one power deeper. -/
theorem sub_homogeneousComponent_mem {n : ℕ} {p : MvPolynomial σ R}
    (hmem : p ∈ varIdeal σ R ^ n) :
    p - homogeneousComponent n p ∈ varIdeal σ R ^ (n + 1) := by
  refine mem_pow_of_homogeneousComponent_eq_zero fun m hm => ?_
  have hhom : (homogeneousComponent n p).IsHomogeneous n := by
    apply homogeneousComponent_isHomogeneous
  have hmem' : (homogeneousComponent n p) ∈ homogeneousSubmodule σ R n := by
    simpa using hhom
  have hself : homogeneousComponent m (homogeneousComponent n p)
      = if m = n then homogeneousComponent n p else 0 :=
    homogeneousComponent_of_mem hmem'
  rw [map_sub, hself]
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with h | h
  · rw [homogeneousComponent_eq_zero_of_mem_pow hmem h, if_neg (by omega), sub_zero]
  · rw [h, if_pos rfl, sub_self]

/-! ## The sharp product -/

/-- **Orders add sharply over a domain.** -/
theorem sharp_product [IsDomain R] {a b : ℕ} {p q : MvPolynomial σ R}
    (hpa : p ∈ varIdeal σ R ^ a) (hpa' : p ∉ varIdeal σ R ^ (a + 1))
    (hqb : q ∈ varIdeal σ R ^ b) (hqb' : q ∉ varIdeal σ R ^ (b + 1)) :
    p * q ∉ varIdeal σ R ^ (a + b + 1) := by
  intro hmem
  have hP0 : homogeneousComponent a p ≠ 0 :=
    homogeneousComponent_ne_zero_of_not_mem hpa hpa'
  have hQ0 : homogeneousComponent b q ≠ 0 :=
    homogeneousComponent_ne_zero_of_not_mem hqb hqb'
  have hPhom : (homogeneousComponent a p).IsHomogeneous a := by
    apply homogeneousComponent_isHomogeneous
  have hQhom : (homogeneousComponent b q).IsHomogeneous b := by
    apply homogeneousComponent_isHomogeneous
  have hPQ0 : homogeneousComponent a p * homogeneousComponent b q ≠ 0 := mul_ne_zero hP0 hQ0
  have hPQhom : (homogeneousComponent a p * homogeneousComponent b q).IsHomogeneous (a + b) :=
    hPhom.mul hQhom
  have hp' : p - homogeneousComponent a p ∈ varIdeal σ R ^ (a + 1) :=
    sub_homogeneousComponent_mem hpa
  have hq' : q - homogeneousComponent b q ∈ varIdeal σ R ^ (b + 1) :=
    sub_homogeneousComponent_mem hqb
  have hPmem : homogeneousComponent a p ∈ varIdeal σ R ^ a := homogeneous_mem_varIdeal_pow hPhom
  have hcross : p * q - homogeneousComponent a p * homogeneousComponent b q
      ∈ varIdeal σ R ^ (a + b + 1) := by
    have hid : p * q - homogeneousComponent a p * homogeneousComponent b q
        = (p - homogeneousComponent a p) * q
          + homogeneousComponent a p * (q - homogeneousComponent b q) := by ring
    rw [hid]
    refine Ideal.add_mem _ ?_ ?_
    · have hmul := Ideal.mul_mem_mul hp' hqb
      rw [← pow_add] at hmul
      have : a + 1 + b = a + b + 1 := by omega
      rwa [this] at hmul
    · have hmul := Ideal.mul_mem_mul hPmem hq'
      rw [← pow_add] at hmul
      have : a + (b + 1) = a + b + 1 := by omega
      rwa [this] at hmul
  have hPQmem : homogeneousComponent a p * homogeneousComponent b q
      ∈ varIdeal σ R ^ (a + b + 1) := by
    have hsub := Ideal.sub_mem _ hmem hcross
    simpa using hsub
  exact homogeneous_not_mem_varIdeal_pow_succ hPQhom hPQ0 hPQmem

end KltDP.RingTheory.MvPolynomialSharpProduct
