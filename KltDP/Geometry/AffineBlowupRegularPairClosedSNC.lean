import KltDP.Geometry.AffineBlowupRegularPairFractionNode
import KltDP.Geometry.StrictNormalCrossings

/-!
# SNC equations at actual closed exceptional chart points

The original exceptional and residual equations, separately or together,
are SNC in a regular two-dimensional closed-point localization. The
maximal-ideal spanning pairs are derived from the original Rees chart.
Regularity and dimension remain explicit, for the proved smooth-surface
stalk producers to supply in the geometric application.
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
variable (P : Ideal (chartRing I a)) [P.IsMaximal]
variable (hcenter : chartCenterIdeal I a ≤ P)
variable (hregular : RegularLocal (Localization.AtPrime P))
variable (hdim : ringKrullDim (Localization.AtPrime P) = 2)

include ha hb hI hcenter hregular hdim in
/-- The original exceptional equation is a member of a derived complete
regular parameter pair at each original closed exceptional point. -/
theorem exceptional_snc_at_closed :
    IsStrictNormalCrossingsEquation (Localization.AtPrime P)
      (algebraMap (chartRing I a) (Localization.AtPrime P) (chartBaseMap I a (a : R))) := by
  obtain ⟨r, hr⟩ := exists_closedPoint_stalk_span I a b ha hb hI P hcenter
  exact IsStrictNormalCrossingsEquation.of_first_parameter hregular hdim _ _ hr

include ha hb hI hcenter hregular hdim in
/-- The original residual fraction is a node parameter where it vanishes,
and a unit away from that actual node. -/
theorem fraction_snc_at_closed :
    IsStrictNormalCrossingsEquation (Localization.AtPrime P)
      (algebraMap (chartRing I a) (Localization.AtPrime P) (chartFraction I a b)) := by
  by_cases ht : chartFraction I a b ∈ P
  · have hpair := fraction_node_stalk_span I a b ha hb hI P hcenter ht
    exact IsStrictNormalCrossingsEquation.of_first_parameter hregular hdim _ _
      (Ideal.span_pair_comm.trans hpair)
  · exact Or.inl (IsLocalization.map_units (Localization.AtPrime P)
      (⟨chartFraction I a b, ht⟩ : P.primeCompl))

include ha hb hI hcenter hregular hdim in
/-- The original reduced exceptional-plus-residual equation is a strict
crossing at the node and a unit multiple of the exceptional parameter elsewhere. -/
theorem exceptional_fraction_snc_at_closed :
    IsStrictNormalCrossingsEquation (Localization.AtPrime P)
      (algebraMap (chartRing I a) (Localization.AtPrime P)
        (chartBaseMap I a (a : R) * chartFraction I a b)) := by
  rw [map_mul]
  by_cases ht : chartFraction I a b ∈ P
  · exact IsStrictNormalCrossingsEquation.of_parameter_product hregular hdim _ _
      (fraction_node_stalk_span I a b ha hb hI P hcenter ht)
  · have hu := IsLocalization.map_units (Localization.AtPrime P)
      (⟨chartFraction I a b, ht⟩ : P.primeCompl)
    obtain ⟨v, hv⟩ := hu
    have hx := exceptional_snc_at_closed I a b ha hb hI P hcenter hregular hdim
    simpa only [hv, mul_comm] using hx.unit_mul v

end KltDP.Geometry.AffineBlowupRegularPairChart
