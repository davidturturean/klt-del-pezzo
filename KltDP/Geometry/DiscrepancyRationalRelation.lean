import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Ordinary rational scalar cancellation in the existing divisor class space. -/

namespace KltDP.Geometry.DiscrepancyRationalRelation

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Solve the integral-pattern relation after the original target class
has been pulled back. All objects remain in the given rational module. -/
theorem solve (p r d : ℚ) (hp : p ≠ 0) (hr : r ≠ 0)
    (K B F M T : V)
    (h : (p * r) • K + (p * r - 2) • B + (r * (p - 2)) • F + d • M = 0)
    (hT : T = (-d / (p * r)) • M) :
    K - T = (-((p * r - 2) / (p * r))) • B - ((p - 2) / p) • F := by
  have hs : p * r ≠ 0 := mul_ne_zero hp hr
  have hscaled := congrArg (fun v : V => (p * r)⁻¹ • v) h
  simp only [smul_add, smul_smul, smul_zero, inv_mul_cancel₀ hs, one_smul] at hscaled
  have hB : (p * r)⁻¹ * (p * r - 2) = (p * r - 2) / (p * r) := by
    rw [div_eq_mul_inv, mul_comm]
  have hF : (p * r)⁻¹ * (r * (p - 2)) = (p - 2) / p := by
    field_simp [hp, hr] <;> ring
  have hM : (p * r)⁻¹ * d = d / (p * r) := by
    rw [div_eq_mul_inv, mul_comm]
  rw [hB, hF, hM] at hscaled
  have hsum : (K - T) +
      (((p * r - 2) / (p * r)) • B + ((p - 2) / p) • F) = 0 := by
    rw [hT, neg_div, neg_smul]
    calc
      _ = K + ((p * r - 2) / (p * r)) • B + ((p - 2) / p) • F +
          (d / (p * r)) • M := by abel
      _ = 0 := hscaled
  calc
    K - T = -(((p * r - 2) / (p * r)) • B + ((p - 2) / p) • F) :=
      eq_neg_of_add_eq_zero_left hsum
    _ = (-((p * r - 2) / (p * r))) • B - ((p - 2) / p) • F := by
      simp only [neg_add, neg_smul, sub_eq_add_neg]

end KltDP.Geometry.DiscrepancyRationalRelation
