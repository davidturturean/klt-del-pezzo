import KltDP.Geometry.AffineBlowupRegularPairClosedSNC
import KltDP.Geometry.AffineBlowupRegularPairResidual

/-!
# Dimension-one SNC equations at the original generic branch ideals

At the actual exceptional or residual generic ideal, localization makes
that branch equation a generator of the whole maximal ideal and makes
the other equation a unit. These are dimension-one parameter systems;
the closed-point dimension-two argument is not reused at generic points.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)
variable (ha : (a : R) ∈ nonZeroDivisors R)
variable (hb : Ideal.Quotient.mk (Ideal.span {(a : R)}) (b : R) ∈
  nonZeroDivisors (R ⧸ Ideal.span {(a : R)}))
variable (hI : I = Ideal.span {(a : R), (b : R)})
variable (P : Ideal (chartRing I a)) [P.IsPrime]
variable (hregular : RegularLocal (Localization.AtPrime P))
variable (hdim : ringKrullDim (Localization.AtPrime P) = 1)

include ha hb hI hregular hdim in
/-- The three original reduced-support choices at the actual generic
exceptional ideal use one parameter and a unit. -/
theorem snc_at_generic_exceptional [I.IsPrime] (hP : P = chartCenterIdeal I a) :
    let ψ := algebraMap (chartRing I a) (Localization.AtPrime P)
    IsStrictNormalCrossingsEquation (Localization.AtPrime P) (ψ (chartBaseMap I a (a : R))) ∧
      IsStrictNormalCrossingsEquation (Localization.AtPrime P) (ψ (chartFraction I a b)) ∧
      IsStrictNormalCrossingsEquation (Localization.AtPrime P)
        (ψ (chartBaseMap I a (a : R) * chartFraction I a b)) := by
  let ψ := algebraMap (chartRing I a) (Localization.AtPrime P)
  have hspan : Ideal.span {ψ (chartBaseMap I a (a : R))} =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    calc
      _ = Ideal.map ψ (chartCenterIdeal I a) := by
        rw [chartCenterIdeal, map_chartBaseMap_ideal, Ideal.map_span, Set.image_singleton]
      _ = Ideal.map ψ P := congrArg (Ideal.map ψ) hP.symm
      _ = _ := Localization.AtPrime.map_eq_maximalIdeal (I := P)
  have ht : chartFraction I a b ∉ P := by
    rw [hP, ← exceptionalCoordinateMap_ker I a b ha hb hI, RingHom.mem_ker,
      exceptionalCoordinateMap_fraction]
    exact Polynomial.X_ne_zero
  have hu : IsUnit (ψ (chartFraction I a b)) :=
    IsLocalization.map_units (Localization.AtPrime P) (⟨chartFraction I a b, ht⟩ : P.primeCompl)
  have hx := IsStrictNormalCrossingsEquation.of_single_parameter hregular hdim _ hspan
  refine ⟨hx, Or.inl hu, ?_⟩
  obtain ⟨v, hv⟩ := hu
  simpa only [map_mul, hv, mul_comm] using hx.unit_mul v

include ha hb hI hregular hdim in
/-- The three original reduced-support choices at the actual generic
residual ideal use one parameter and a unit. -/
theorem snc_at_generic_residual (hP : P = Ideal.span {chartFraction I a b})
    (hab : (a : R) ∉ Ideal.span {(b : R)}) :
    let ψ := algebraMap (chartRing I a) (Localization.AtPrime P)
    IsStrictNormalCrossingsEquation (Localization.AtPrime P) (ψ (chartBaseMap I a (a : R))) ∧
      IsStrictNormalCrossingsEquation (Localization.AtPrime P) (ψ (chartFraction I a b)) ∧
      IsStrictNormalCrossingsEquation (Localization.AtPrime P)
        (ψ (chartBaseMap I a (a : R) * chartFraction I a b)) := by
  let ψ := algebraMap (chartRing I a) (Localization.AtPrime P)
  have hspan : Ideal.span {ψ (chartFraction I a b)} =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    calc
      _ = Ideal.map ψ (Ideal.span {chartFraction I a b}) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map ψ P := congrArg (Ideal.map ψ) hP.symm
      _ = _ := Localization.AtPrime.map_eq_maximalIdeal (I := P)
  have hx : chartBaseMap I a (a : R) ∉ P := by
    rw [hP]
    exact parameter_not_mem_residual I a b ha hb hI hab
  have hu : IsUnit (ψ (chartBaseMap I a (a : R))) :=
    IsLocalization.map_units (Localization.AtPrime P)
      (⟨chartBaseMap I a (a : R), hx⟩ : P.primeCompl)
  have ht := IsStrictNormalCrossingsEquation.of_single_parameter hregular hdim _ hspan
  refine ⟨Or.inl hu, ht, ?_⟩
  obtain ⟨v, hv⟩ := hu
  simpa only [map_mul, hv] using ht.unit_mul v

end KltDP.Geometry.AffineBlowupRegularPairChart
