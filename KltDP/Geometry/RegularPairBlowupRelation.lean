import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring

/-!
# The exceptional parameter in the regular-pair chart relation

For a regular pair `f,g`, the image of `f` remains a nonzerodivisor in
the actual quotient `R[T]/(f*T-g)`. Reduction of polynomial coefficients
modulo `f`, followed by the original regularity of `g` in `R/(f)`,
proves the needed cancellation. This is the algebraic input for the
existing original Rees-chart lift; no chart presentation is assumed.
-/

noncomputable section

namespace KltDP.Geometry.RegularPairBlowupRelation

open Polynomial

universe u

variable {R : Type u} [CommRing R] (f g : R)

/-- The coefficient reduction detects the divisibility forced by the
literal equation defining the prospective regular-pair chart. -/
theorem cofactor_divisible
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      nonZeroDivisors (R ⧸ Ideal.span {f}))
    (P Q : Polynomial R)
    (h : C f * P = (C f * X - C g) * Q) : C f ∣ Q := by
  let π := Ideal.Quotient.mk (Ideal.span {f})
  have hfzero : π f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
  have hmap := congrArg (Polynomial.map π) h
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
    Polynomial.map_X, hfzero, C_0, zero_mul, zero_sub] at hmap
  have hzero : C (π g) * Q.map π = 0 := by
    simpa only [neg_mul, neg_eq_zero] using hmap.symm
  have hC : C (π g) ∈ nonZeroDivisors (Polynomial (R ⧸ Ideal.span {f})) :=
    Polynomial.mem_nonzeroDivisors_of_coeff_mem 0 (by simpa only [coeff_C_zero] using hg)
  have hQ : Q.map π = 0 := (mul_left_mem_nonZeroDivisors_eq_zero_iff hC).mp hzero
  apply (Polynomial.C_dvd_iff_dvd_coeff f Q).mpr
  intro n
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using
    congrArg (fun A : Polynomial (R ⧸ Ideal.span {f}) => A.coeff n) hQ

/-- The original first parameter remains regular in the literal
`f*T-g` quotient, proved from the original regular-pair hypotheses. -/
theorem parameter_mem_nonZeroDivisors (hf : f ∈ nonZeroDivisors R)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      nonZeroDivisors (R ⧸ Ideal.span {f})) :
    Ideal.Quotient.mk (Ideal.span {C f * X - C g}) (C f) ∈
      nonZeroDivisors (Polynomial R ⧸ Ideal.span {C f * X - C g}) := by
  apply _root_.mem_nonZeroDivisors_iff.mpr
  intro z hz
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hprod : C f * P ∈ Ideal.span {C f * X - C g} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, mul_comm] using hz
  obtain ⟨Q, hQ⟩ := Ideal.mem_span_singleton.mp hprod
  obtain ⟨T, hT⟩ := cofactor_divisible f g hg P Q hQ
  have hC : C f ∈ nonZeroDivisors (Polynomial R) :=
    Polynomial.mem_nonzeroDivisors_of_coeff_mem 0 (by simpa only [coeff_C_zero] using hf)
  apply Ideal.mem_span_singleton.mpr
  refine ⟨T, ?_⟩
  apply (mul_cancel_left_mem_nonZeroDivisors hC).mp
  calc
    C f * P = (C f * X - C g) * Q := hQ
    _ = C f * ((C f * X - C g) * T) := by rw [hT]; ring

end KltDP.Geometry.RegularPairBlowupRelation
