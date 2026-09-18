import KltDP.Geometry.AffineBlowupRegularPairExceptionalDVR
import KltDP.Geometry.AffineBlowupRegularPairGenericSNC
import KltDP.Geometry.RegularLocalDimensionTwo

/-!
# Derived generic exceptional regularity and SNC

The original regular-pair exceptional localization is already proved to
be a DVR. Its pinned cotangent rank-one formula, together with the proved
normal local-domain regularity criterion, supplies regularity and actual
Krull dimension one. The original exceptional/fraction/product SNC
formulas therefore require no generic regularity or dimension premise.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable (I : Ideal R) (a b : I)
variable (ha : (a : R) ∈ nonZeroDivisors R)
variable (hb : Ideal.Quotient.mk (Ideal.span {(a : R)}) (b : R) ∈
  nonZeroDivisors (R ⧸ Ideal.span {(a : R)}))
variable (hI : I = Ideal.span {(a : R), (b : R)}) [I.IsPrime]

/-- The actual exceptional generic local ring is regular of dimension one,
with both conclusions derived from its already proved DVR structure. -/
theorem exceptionalGenericLocalRing_regular_dimension :
    RegularLocal (exceptionalGenericLocalRing I a b ha hb hI) ∧
      ringKrullDim (exceptionalGenericLocalRing I a b ha hb hI) = 1 := by
  let L := exceptionalGenericLocalRing I a b ha hb hI
  letI : IsDomain L := exceptionalGenericLocalRing_isDomain I a b ha hb hI
  letI : IsNoetherianRing L :=
    exceptionalGenericLocalRing_isNoetherianRing I a b ha hb hI
  letI : IsDiscreteValuationRing L :=
    exceptionalGenericLocalRing_isDiscreteValuationRing I a b ha hb hI
  have hrank := IsLocalRing.finrank_CotangentSpace_eq_one L
  have hregular : RegularLocal L :=
    regularLocal_of_isIntegrallyClosed_of_ringKrullDim_le_one L
      (ringKrullDim_le_one_of_finrank_cotangentSpace_le_one L hrank.le)
  refine ⟨hregular, ?_⟩
  simpa only [hrank, Nat.cast_one] using hregular.2

include ha hb hI in
/-- At the original generic exceptional prime, all three literal reduced
support equations are SNC without supplied local regularity or dimension. -/
theorem snc_at_generic_exceptional_of_regularPair
    (P : Ideal (chartRing I a)) [P.IsPrime] (hP : P = chartCenterIdeal I a) :
    let ψ := algebraMap (chartRing I a) (Localization.AtPrime P)
    IsStrictNormalCrossingsEquation (Localization.AtPrime P)
        (ψ (chartBaseMap I a (a : R))) ∧
      IsStrictNormalCrossingsEquation (Localization.AtPrime P)
        (ψ (chartFraction I a b)) ∧
      IsStrictNormalCrossingsEquation (Localization.AtPrime P)
        (ψ (chartBaseMap I a (a : R) * chartFraction I a b)) := by
  subst P
  have hlocal := exceptionalGenericLocalRing_regular_dimension I a b ha hb hI
  exact snc_at_generic_exceptional I a b ha hb hI (chartCenterIdeal I a)
    hlocal.1 hlocal.2 rfl

end KltDP.Geometry.AffineBlowupRegularPairChart
