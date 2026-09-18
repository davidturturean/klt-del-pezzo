import KltDP.Geometry.AffineBlowupRegularPairExceptionalGeneric
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# The original exceptional generic localization is a DVR

The actual chart embeds in the localization of the original domain and
is Noetherian by its proved relation-ring presentation. Its exceptional
generic localization has the proved nonzero principal maximal ideal.
The pinned Noetherian local-domain criterion therefore supplies the DVR;
the original first parameter is its uniformizer.
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

include ha in
/-- The original Rees chart is a domain by its actual injection into
the localization at the original nonzero parameter. -/
theorem chartRing_isDomain_of_parameter [IsDomain R] : IsDomain (chartRing I a) := by
  have hne : (a : R) ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨(a : R), ha⟩
  letI : IsDomain (Localization.Away (a : R)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors R
      (powers_le_nonZeroDivisors_of_noZeroDivisors hne)
  exact Function.Injective.isDomain (chartToLocalization I a)
    (chartToLocalization_injective I a)

include ha hb hI in
/-- Noetherianity is transported through the proved original relation
presentation, without a new finiteness assumption on the chart. -/
theorem chartRing_isNoetherianRing_of_regularPair [IsNoetherianRing R] :
    IsNoetherianRing (chartRing I a) := by
  letI : IsNoetherianRing (relationRing I a b) := inferInstance
  exact isNoetherianRing_of_ringEquiv (relationRing I a b)
    (chartRelationEquiv I a b ha hb hI).symm

variable [I.IsPrime]

/-- The actual exceptional generic localization is a domain. -/
theorem exceptionalGenericLocalRing_isDomain [IsDomain R] :
    IsDomain (exceptionalGenericLocalRing I a b ha hb hI) := by
  letI : IsDomain (chartRing I a) := chartRing_isDomain_of_parameter I a ha
  infer_instance

/-- The actual exceptional generic localization is Noetherian. -/
theorem exceptionalGenericLocalRing_isNoetherianRing [IsNoetherianRing R] :
    IsNoetherianRing (exceptionalGenericLocalRing I a b ha hb hI) := by
  letI : IsNoetherianRing (chartRing I a) :=
    chartRing_isNoetherianRing_of_regularPair I a b ha hb hI
  exact IsLocalization.isNoetherianRing
    (exceptionalGenericPrime I a b ha hb hI).asIdeal.primeCompl
    (exceptionalGenericLocalRing I a b ha hb hI) inferInstance

/-- The image of the original first parameter is irreducible in the
actual exceptional generic localization. -/
theorem exceptionalGenericParameter_irreducible [IsDomain R] :
    Irreducible (exceptionalGenericParameter I a b ha hb hI) := by
  letI : IsDomain (exceptionalGenericLocalRing I a b ha hb hI) :=
    exceptionalGenericLocalRing_isDomain I a b ha hb hI
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
    (exceptionalGenericParameter I a b ha hb hI)
    (exceptionalGenericParameter_ne_zero I a b ha hb hI)
    (maximalIdeal_eq_span_exceptionalGenericParameter I a b ha hb hI)

/-- The original exceptional generic localization is a DVR, derived
from its actual nonzero principal maximal ideal. -/
theorem exceptionalGenericLocalRing_isDiscreteValuationRing
    [IsDomain R] [IsNoetherianRing R] :
    letI : IsDomain (exceptionalGenericLocalRing I a b ha hb hI) :=
      exceptionalGenericLocalRing_isDomain I a b ha hb hI
    IsDiscreteValuationRing (exceptionalGenericLocalRing I a b ha hb hI) := by
  let L := exceptionalGenericLocalRing I a b ha hb hI
  letI : IsDomain L := exceptionalGenericLocalRing_isDomain I a b ha hb hI
  letI : IsNoetherianRing L :=
    exceptionalGenericLocalRing_isNoetherianRing I a b ha hb hI
  have hirr := exceptionalGenericParameter_irreducible I a b ha hb hI
  have hnot : ¬ IsField L := by
    intro hfield
    letI : Field L := hfield.toField
    exact hirr.not_isUnit (isUnit_iff_ne_zero.mpr hirr.ne_zero)
  have hprincipal : (IsLocalRing.maximalIdeal L).IsPrincipal := by
    refine ⟨⟨exceptionalGenericParameter I a b ha hb hI, ?_⟩⟩
    exact maximalIdeal_eq_span_exceptionalGenericParameter I a b ha hb hI
  exact ((IsDiscreteValuationRing.TFAE L hnot).out 4 0).mp hprincipal

end KltDP.Geometry.AffineBlowupRegularPairChart
