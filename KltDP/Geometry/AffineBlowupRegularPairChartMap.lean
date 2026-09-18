import KltDP.Geometry.RegularPairBlowupRelation
import KltDP.Geometry.AffineBlowupLift
import KltDP.Geometry.AffineBlowupChartCenter

/-!
# The original Rees-chart map to the regular-pair relation quotient

The target is the literal polynomial quotient `R[T]/(a*T-b)`. Its first
parameter is proved regular, so the existing original Rees-chart lift
applies. Both the original base-ring map and original homogeneous fraction
are preserved. A presentation isomorphism is not a premise.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup Polynomial

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

/-- The literal one-relation quotient for the original ordered generators. -/
abbrev relationRing :=
  Polynomial R ⧸ Ideal.span {C (a : R) * X - C (b : R)}

/-- The original base map into that relation quotient. -/
def quotientBaseMap : R →+* relationRing I a b :=
  (Ideal.Quotient.mk _).comp C

/-- The original polynomial variable in the relation quotient. -/
def quotientFraction : relationRing I a b := Ideal.Quotient.mk _ X

theorem quotientBaseMap_relation :
    quotientBaseMap I a b (a : R) * quotientFraction I a b =
      quotientBaseMap I a b (b : R) := by
  have h : Ideal.Quotient.mk (Ideal.span {C (a : R) * X - C (b : R)})
      (C (a : R) * X - C (b : R)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [map_sub, map_mul, sub_eq_zero] at h
  exact h

theorem quotientBaseMap_regular (ha : (a : R) ∈ nonZeroDivisors R)
    (hb : Ideal.Quotient.mk (Ideal.span {(a : R)}) (b : R) ∈
      nonZeroDivisors (R ⧸ Ideal.span {(a : R)})) :
    quotientBaseMap I a b (a : R) ∈ nonZeroDivisors (relationRing I a b) :=
  RegularPairBlowupRelation.parameter_mem_nonZeroDivisors (a : R) (b : R) ha hb

theorem quotientBaseMap_center (hI : I = Ideal.span {(a : R), (b : R)}) :
    Ideal.map (quotientBaseMap I a b) I ≤
      Ideal.span {quotientBaseMap I a b (a : R)} := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply hI.le.trans
  apply Ideal.span_le.mpr
  intro z hz
  rcases hz with rfl | hz
  · exact Ideal.mem_span_singleton_self _
  · rw [Set.mem_singleton_iff] at hz
    subst z
    exact Ideal.mem_span_singleton.mpr
      ⟨quotientFraction I a b, (quotientBaseMap_relation I a b).symm⟩

variable (ha : (a : R) ∈ nonZeroDivisors R)
variable (hb : Ideal.Quotient.mk (Ideal.span {(a : R)}) (b : R) ∈
  nonZeroDivisors (R ⧸ Ideal.span {(a : R)}))
variable (hI : I = Ideal.span {(a : R), (b : R)})

/-- The actual Rees-chart lift, with both of its hypotheses now proved. -/
def toQuotient : chartRing I a →+* relationRing I a b :=
  chartLift I a (quotientBaseMap I a b)
    (quotientBaseMap_regular I a b ha hb) (quotientBaseMap_center I a b hI)

theorem toQuotient_baseMap (r : R) :
    toQuotient I a b ha hb hI (chartBaseMap I a r) = quotientBaseMap I a b r :=
  chartLift_baseMap I a (quotientBaseMap I a b)
    (quotientBaseMap_regular I a b ha hb) (quotientBaseMap_center I a b hI) r

theorem toQuotient_fraction :
    toQuotient I a b ha hb hI (chartFraction I a b) = quotientFraction I a b := by
  apply (mul_cancel_left_mem_nonZeroDivisors
    (quotientBaseMap_regular I a b ha hb)).mp
  rw [quotientBaseMap_relation]
  have h := congrArg (toQuotient I a b ha hb hI) (chartBaseMap_mul_chartFraction I a b)
  simpa only [map_mul, toQuotient_baseMap] using h

end KltDP.Geometry.AffineBlowupRegularPairChart
