import KltDP.Geometry.RegularSurfaceBlowupResidualClosure
import KltDP.Geometry.AffineBlowupRegularPairExceptionalGeneric

/-!
# Actual reduced ideals of the regular surface blowup boundary

The original residual strict-support closure has the actual fraction as
its prime vanishing ideal. The product of the exceptional equation and
that fraction is itself radical, because these are distinct original
prime principal ideals. Thus the existing pullback radical formula gives
an equality with the literal reduced principal ideal, not merely another
radical expression. All primality and distinctness facts are derived
from the given original regular surface parameters.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup

universe u

private theorem inf_span_eq_span_mul {S : Type u} [CommRing S]
    (x t : S) (ht : (Ideal.span {t}).IsPrime) (hx : x ∉ Ideal.span {t}) :
    Ideal.span {x} ⊓ Ideal.span {t} = Ideal.span {x * t} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hz.1
    have hr : r ∈ Ideal.span {t} := (ht.mem_or_mem hz.2).resolve_left hx
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hr
    exact Ideal.mem_span_singleton.mpr ⟨s, (mul_assoc x t s).symm⟩
  · rw [← Ideal.span_singleton_mul_span_singleton]
    exact Ideal.mul_le_inf

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable (I : Ideal R) (a b : I)
variable (hR : RegularLocal R) (hdim : ringKrullDim R = 2)
variable (hI : I = Ideal.span {(a : R), (b : R)}) (hmax : I = maximalIdeal R)

include hR hdim hI hmax in
/-- The actual chartwise strict-transform closure has the literal residual prime ideal. -/
theorem original_parameter_branch_vanishingIdeal :
    PrimeSpectrum.vanishingIdeal
      (closure ((chartι I a ≫ toSpec I).base ⁻¹'
        (PrimeSpectrum.zeroLocus {(b : R)} \ PrimeSpectrum.zeroLocus (I : Set R)))) =
      Ideal.span {chartFraction I a b} := by
  rw [original_parameter_branch_closure I a b hR hdim hI hmax,
    ← PrimeSpectrum.zeroLocus_span, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  exact (fraction_ideal_isPrime_of_surface_parameters I a b hR hdim hI hmax).isRadical.radical

include hR hdim hI hmax in
/-- The literal exceptional-times-residual equation already defines a reduced ideal. -/
theorem exceptional_fraction_span_radical :
    (Ideal.span {chartBaseMap I a (a : R) * chartFraction I a b}).radical =
      Ideal.span {chartBaseMap I a (a : R) * chartFraction I a b} := by
  have hspan := hI.symm.trans hmax
  have hpair := RegularLocalTwoParameters.regular_pair hR hdim (a : R) (b : R) hspan
  letI : I.IsPrime := hmax.symm ▸ (inferInstance : (maximalIdeal R).IsPrime)
  have hxprime := chartCenterIdeal_isPrime I a b hpair.1 hpair.2 hI
  rw [chartCenterIdeal, map_chartBaseMap_ideal] at hxprime
  have htprime := fraction_ideal_isPrime_of_surface_parameters I a b hR hdim hI hmax
  have hab : (a : R) ∉ Ideal.span {(b : R)} :=
    RegularLocalTwoParameters.second_not_mem_first hR hdim (b : R) (a : R)
      (Ideal.span_pair_comm.trans hspan)
  have hxt := inf_span_eq_span_mul (chartBaseMap I a (a : R)) (chartFraction I a b)
    htprime (parameter_not_mem_residual I a b hpair.1 hpair.2 hI hab)
  calc
    _ = (Ideal.span {chartBaseMap I a (a : R)} ⊓ Ideal.span {chartFraction I a b}).radical :=
      congrArg Ideal.radical hxt.symm
    _ = _ := (hxprime.isRadical.inf htprime.isRadical).radical
    _ = _ := hxt

include hR hdim hI hmax in
/-- The original exceptional plus two-branch total transform has this actual reduced ideal. -/
theorem reduced_exceptional_pair_ideal :
    (chartCenterIdeal I a *
      Ideal.map (chartBaseMap I a) (Ideal.span {(a : R) * (b : R)})).radical =
      Ideal.span {chartBaseMap I a (a : R) * chartFraction I a b} :=
  (chart_exceptional_boundary_pair_radical I a b).trans
    (exceptional_fraction_span_radical I a b hR hdim hI hmax)

end KltDP.Geometry.AffineBlowupRegularPairChart
