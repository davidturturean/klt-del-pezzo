import KltDP.Geometry.AffineBlowupRegularPairClosedPoint
import Mathlib.RingTheory.Localization.AtPrime

/-!
# Actual localized generators at closed exceptional points

Localization of the proved original closed-point ideal gives the maximal
ideal of the original chart's prime localization. Both generators are
images under its original localization map.
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
attribute [local instance] Ideal.Quotient.field

variable [I.IsMaximal] [IsAlgClosed (R ⧸ I)]

include ha hb hI in
/-- At an actual closed exceptional point, the original exceptional
parameter and shifted original fraction generate the localized maximal ideal. -/
theorem exists_closedPoint_stalk_span (P : Ideal (chartRing I a)) [P.IsMaximal]
    (hcenter : chartCenterIdeal I a ≤ P) :
    ∃ r : R, Ideal.span {
      algebraMap (chartRing I a) (Localization.AtPrime P) (chartBaseMap I a (a : R)),
      algebraMap (chartRing I a) (Localization.AtPrime P) (chartFraction I a b) -
        algebraMap (chartRing I a) (Localization.AtPrime P) (chartBaseMap I a r)} =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  obtain ⟨r, hr⟩ := exists_closedPoint_ideal_eq I a b ha hb hI P hcenter
  refine ⟨r, ?_⟩
  let ψ := algebraMap (chartRing I a) (Localization.AtPrime P)
  calc
    _ = Ideal.map ψ (Ideal.span {chartBaseMap I a (a : R),
        chartFraction I a b - chartBaseMap I a r}) := by
      rw [Ideal.map_span, Set.image_pair, map_sub]
    _ = Ideal.map ψ P := congrArg (Ideal.map ψ) hr.symm
    _ = _ := Localization.AtPrime.map_eq_maximalIdeal (I := P)

end KltDP.Geometry.AffineBlowupRegularPairChart
