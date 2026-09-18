import KltDP.Geometry.PointBlowupExceptionalPrimeStalk
import KltDP.Geometry.AffineBlowupRegularPairExceptionalOrder

/-!
# The original exceptional curve stalk and its actual parameter coordinates

The actual prime equality is proved in the preceding module. Transport
along that equality preserves every original localization numerator.
Composing with the original whole-chart stalk equivalence identifies the
original source curve stalk with the literal exceptional localization,
and retains the original chart and original base coefficients.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupExceptionalPrimeStalk

open AffineBlowup AffineBlowupChartBaseChange AffineBlowupRegularPairChart
open PointBlowupGluing PointBlowupChartStalk

private def localizationAtPrimeEquivOfEq {A : Type u} [CommRing A]
    (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (h : P = Q) :
    Localization.AtPrime P ≃+* Localization.AtPrime Q := by
  subst Q
  exact RingEquiv.refl _

private theorem localizationAtPrimeEquivOfEq_algebraMap {A : Type u} [CommRing A]
    (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (h : P = Q) (r : A) :
    localizationAtPrimeEquivOfEq P Q h (algebraMap A (Localization.AtPrime P) r) =
      algebraMap A (Localization.AtPrime Q) r := by
  subst Q
  rfl

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (C : (sourceSurface X j q hclosed).PrimeCurve)
    (a : q.asIdeal) (P : PrimeSpectrum (chartRing q.asIdeal a))
    (hC : (chartInclusion j q hclosed a).base P = C.genericPoint)
    (hcenter : (projection j q hclosed).base C.genericPoint = j.base q)

local instance : (centerIdeal q).IsPrime := by
  dsimp only [centerIdeal]
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  infer_instance

variable (b : centerIdeal q)
    (ha : (centerParameter q a : Localization.AtPrime q.asIdeal) ∈
      nonZeroDivisors (Localization.AtPrime q.asIdeal))
    (hb : Ideal.Quotient.mk
      (Ideal.span {(centerParameter q a : Localization.AtPrime q.asIdeal)})
      (b : Localization.AtPrime q.asIdeal) ∈ nonZeroDivisors
        (Localization.AtPrime q.asIdeal ⧸
          Ideal.span {(centerParameter q a : Localization.AtPrime q.asIdeal)}))
    (hI : centerIdeal q = Ideal.span
      {(centerParameter q a : Localization.AtPrime q.asIdeal),
        (b : Localization.AtPrime q.asIdeal)})

/-- The original source curve stalk is the literal exceptional generic
localization. Both constituent stalk maps and the prime equality are proved. -/
def exceptionalStalkEquiv :
    (sourceSurface X j q hclosed).stalk C.genericPoint ≃+*
      exceptionalGenericLocalRing (centerIdeal q) (centerParameter q a) b ha hb hI := by
  let hPq := chartPrime_comap X j q hclosed C a P hC hcenter
  let Q := localizedChartPrime q.asIdeal a q.asIdeal P.asIdeal hPq
  let J := chartCenterIdeal (centerIdeal q) (centerParameter q a)
  letI : J.IsPrime :=
    chartCenterIdeal_isPrime (centerIdeal q) (centerParameter q a) b ha hb hI
  exact (((scheme j q hclosed).presheaf.stalkCongr
      (.of_eq hC)).commRingCatIsoToRingEquiv).symm.trans
    ((globalStalkEquiv j q hclosed a P hPq).trans
      (localizationAtPrimeEquivOfEq Q J
        (localizedPrime_eq_chartCenterIdeal X j q hclosed C a P hC hcenter b ha hb hI)))

/-- Every actual Rees-chart coefficient is preserved, including its
original map into the whole source stalk and the original base localization. -/
theorem exceptionalStalkEquiv_chartCoefficient (z : chartRing q.asIdeal a) :
    exceptionalStalkEquiv X j q hclosed C a P hC hcenter b ha hb hI
      (((scheme j q hclosed).presheaf.stalkCongr (.of_eq hC)).hom
        ((openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P).symm
          (algebraMap _ (Localization.AtPrime P.asIdeal) z))) =
      algebraMap _
        (exceptionalGenericLocalRing (centerIdeal q) (centerParameter q a) b ha hb hI)
        (chartMap q.asIdeal (algebraMap R (Localization.AtPrime q.asIdeal)) a z) := by
  let hPq := chartPrime_comap X j q hclosed C a P hC hcenter
  let Q := localizedChartPrime q.asIdeal a q.asIdeal P.asIdeal hPq
  let J := chartCenterIdeal (centerIdeal q) (centerParameter q a)
  letI : J.IsPrime :=
    chartCenterIdeal_isPrime (centerIdeal q) (centerParameter q a) b ha hb hI
  let hQ := localizedPrime_eq_chartCenterIdeal X j q hclosed C a P hC hcenter b ha hb hI
  let g := ((scheme j q hclosed).presheaf.stalkCongr (.of_eq hC)).commRingCatIsoToRingEquiv
  change localizationAtPrimeEquivOfEq Q J hQ
    (globalStalkEquiv j q hclosed a P hPq
      (g.symm (g ((openImmersionStalkLocalizationEquiv
        (chartInclusion j q hclosed a) P).symm
          (algebraMap _ (Localization.AtPrime P.asIdeal) z))))) = _
  rw [RingEquiv.symm_apply_apply, globalStalkEquiv_chartCoefficient]
  exact localizationAtPrimeEquivOfEq_algebraMap Q J hQ
    (chartMap q.asIdeal (algebraMap R (Localization.AtPrime q.asIdeal)) a z)

/-- The square retains each original base coefficient, through the
original chart base map and the original centre localization. -/
theorem exceptionalStalkEquiv_baseCoefficient (r : R) :
    exceptionalStalkEquiv X j q hclosed C a P hC hcenter b ha hb hI
      (((scheme j q hclosed).presheaf.stalkCongr (.of_eq hC)).hom
        ((openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P).symm
          (algebraMap _ (Localization.AtPrime P.asIdeal) (chartBaseMap q.asIdeal a r)))) =
      exceptionalGenericBaseMap (centerIdeal q) (centerParameter q a) b ha hb hI
        (algebraMap R (Localization.AtPrime q.asIdeal) r) := by
  rw [exceptionalStalkEquiv_chartCoefficient, chartMap_baseMap]
  rfl

end KltDP.Geometry.PointBlowupExceptionalPrimeStalk
