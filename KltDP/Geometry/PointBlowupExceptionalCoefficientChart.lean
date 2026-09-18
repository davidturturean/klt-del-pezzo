import KltDP.Geometry.CartierCoefficientUniformizer
import KltDP.Geometry.PointBlowupExceptionalEquationChart
import KltDP.Geometry.PointBlowupExceptionalPullbackParameter

/-!
# Coefficient one for the original exceptional equation

The actual exceptional Cartier equation on an original parameter chart
has the same original germ as the proved pulled first parameter. The
existing exceptional-stalk computation makes that germ a uniformizer;
the original Cartier-to-Weil coefficient is therefore one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupExceptionalPrimeStalk

open AffineBlowup PointBlowupGluing PointBlowupChartStalk PointBlowupExceptionalCartier

/-- An original parameter chart over the original centre gives
coefficient one for the actual exceptional Cartier divisor. -/
theorem exceptionalCartierDivisor_coefficient_eq_one_of_chart
    {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (C : (sourceSurface X j q hclosed).PrimeCurve)
    (a : q.asIdeal) (P : PrimeSpectrum (chartRing q.asIdeal a))
    (hC : (chartInclusion j q hclosed a).base P = C.genericPoint)
    (hcenter : (projection j q hclosed).base C.genericPoint = j.base q)
    (b : centerIdeal q)
    (ha : (centerParameter q a : Localization.AtPrime q.asIdeal) ∈
      nonZeroDivisors (Localization.AtPrime q.asIdeal))
    (hb : Ideal.Quotient.mk
      (Ideal.span {(centerParameter q a : Localization.AtPrime q.asIdeal)})
      (b : Localization.AtPrime q.asIdeal) ∈ nonZeroDivisors
        (Localization.AtPrime q.asIdeal ⧸
          Ideal.span {(centerParameter q a : Localization.AtPrime q.asIdeal)}))
    (hI : centerIdeal q = Ideal.span
      {(centerParameter q a : Localization.AtPrime q.asIdeal),
        (b : Localization.AtPrime q.asIdeal)}) :
    letI : IsIntegral (PointBlowupGluing.scheme j q hclosed) :=
      (sourceSurface X j q hclosed).integral
    (sourceSurface X j q hclosed).cartierToWeilHom
      (exceptionalCartierDivisor j q hclosed) C = 1 := by
  letI : IsIntegral (PointBlowupGluing.scheme j q hclosed) :=
    (sourceSurface X j q hclosed).integral
  let c := exceptionalEquationChart j q hclosed a P
  have hx : C.genericPoint ∈ c.chart.openSet := by
    change C.genericPoint ∈ chartInclusion j q hclosed a ''ᵁ ⊤
    rw [← hC]
    exact mem_chart_image_top (chartInclusion j q hclosed a) P
  have hg :
      (((PointBlowupGluing.scheme j q hclosed).presheaf.stalkCongr (.of_eq hC)).hom)
        ((openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P).symm
          (algebraMap _ (Localization.AtPrime P.asIdeal) (chartBaseMap q.asIdeal a (a : R)))) =
      (PointBlowupGluing.scheme j q hclosed).presheaf.germ
        c.chart.openSet C.genericPoint hx c.coefficient := by
    rw [openImmersionStalkLocalizationEquiv_symm_algebraMap]
    exact ConcreteCategory.congr_hom
      ((PointBlowupGluing.scheme j q hclosed).presheaf.germ_stalkSpecializes
        (mem_chart_image_top (chartInclusion j q hclosed a) P)
        (Inseparable.of_eq hC).ge)
      ((KltDP.Geometry.chartSectionsEquiv (chartInclusion j q hclosed a)).symm
        (chartBaseMap q.asIdeal a (a : R)))
  have hr := pullback_firstParameter_irreducible X j q hclosed C a P hC hcenter b ha hb hI
  rw [pullback_baseCoefficientGerm] at hr
  exact (sourceSurface X j q hclosed).cartierToWeilHom_eq_one_of_irreducible_germ
    (exceptionalCartierDivisor j q hclosed) c C hx (Eq.mp (congrArg Irreducible hg) hr)

end KltDP.Geometry.PointBlowupExceptionalPrimeStalk

#check @KltDP.Geometry.PointBlowupExceptionalPrimeStalk.exceptionalCartierDivisor_coefficient_eq_one_of_chart
#print axioms KltDP.Geometry.PointBlowupExceptionalPrimeStalk.exceptionalCartierDivisor_coefficient_eq_one_of_chart
