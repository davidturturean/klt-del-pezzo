import KltDP.Geometry.PointBlowupParameterChartSNC
import KltDP.Geometry.AffineBlowupRegularPairGenericRegularSNC
import KltDP.Geometry.AffineBlowupRegularPairExceptionalPoints

/-!
# SNC at every actual parameter-chart point over the original centre

The proved exceptional polynomial quotient classifies every original
chart prime above the centre as generic exceptional or maximal. The
actual smooth surface and its original point blowup supply all local
regularity and dimension facts in the two cases. The given boundary
parameters are retained, including the original exceptional equation,
original residual fraction and their reduced product.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open AffineBlowup AffineBlowupRegularPairChart LocalizedParameterReesChart

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
variable {R : Type u} [CommRing R]
variable (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]

/-- All original points over the centre satisfy the shared SNC equation
predicate for each of the three actual reduced-support choices. -/
theorem pointBlowup_parameter_chart_snc_over_center
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (f g : localCenter q.asIdeal)
    (hfg : Ideal.span {(f : Localization.AtPrime q.asIdeal),
      (g : Localization.AtPrime q.asIdeal)} = localCenter q.asIdeal)
    (P : Ideal (chartRing (localCenter q.asIdeal) f)) [P.IsPrime]
    (hcenter : chartCenterIdeal (localCenter q.asIdeal) f ≤ P) :
    let ψ := algebraMap (chartRing (localCenter q.asIdeal) f) (Localization.AtPrime P)
    IsStrictNormalCrossingsEquation (Localization.AtPrime P)
        (ψ (chartBaseMap (localCenter q.asIdeal) f (f : Localization.AtPrime q.asIdeal))) ∧
      IsStrictNormalCrossingsEquation (Localization.AtPrime P)
        (ψ (chartFraction (localCenter q.asIdeal) f g)) ∧
      IsStrictNormalCrossingsEquation (Localization.AtPrime P)
        (ψ (chartBaseMap (localCenter q.asIdeal) f (f : Localization.AtPrime q.asIdeal) *
          chartFraction (localCenter q.asIdeal) f g)) := by
  have hmax : localCenter q.asIdeal =
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal)
  letI : (localCenter q.asIdeal).IsMaximal :=
    hmax.symm ▸ (inferInstance :
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).IsMaximal)
  letI : IsDomain (Localization.AtPrime q.asIdeal) := X.affineLocalization_isDomain j q
  letI : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    X.affineLocalization_isNoetherianRing j q
  let e := openImmersionStalkLocalizationEquiv j q
  have hR : RegularLocal (Localization.AtPrime q.asIdeal) :=
    regularLocal_of_ringEquiv e (X.regularPoints_of_isSmooth (j.base q))
  have hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 2 :=
    (ringKrullDim_eq_of_ringEquiv e).symm.trans
      (X.closed_stalk_dimension_two (j.base q) hclosed)
  have hpair := RegularLocalTwoParameters.regular_pair hR hdim
    (f : Localization.AtPrime q.asIdeal) (g : Localization.AtPrime q.asIdeal) (hfg.trans hmax)
  rcases exceptional_prime_eq_center_or_maximal (localCenter q.asIdeal) f g
      hpair.1 hpair.2 hfg.symm P hcenter with hgeneric | hclosedP
  · exact snc_at_generic_exceptional_of_regularPair (localCenter q.asIdeal) f g
      hpair.1 hpair.2 hfg.symm P hgeneric
  · letI : P.IsMaximal := hclosedP
    exact X.pointBlowup_parameter_chart_snc_at_closed j q hclosed f g hfg P hcenter

end KltDP.Geometry.NormalProjectiveSurface
