import KltDP.Geometry.PointBlowupExceptionalCoefficientChart
import KltDP.Geometry.PointBlowupExceptionalCoefficientOffCenter
import KltDP.Geometry.PointBlowupSNCOriginalParameters
import KltDP.Geometry.PointBlowupOriginalParameterChartCover

/-!
# The actual exceptional Cartier coefficients of a point blowup

The original smooth surface supplies a genuine regular pair at the
original closed centre. Their original numerators cover each actual
point over that centre. On the selected original chart the actual
exceptional equation is a uniformizer. Thus every original prime over
the centre has coefficient one; the imported off-centre result gives zero.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.PointBlowupExceptionalPrimeStalk

open PointBlowupGluing PointBlowupChartStalk PointBlowupExceptionalCartier

/-- The original exceptional Cartier divisor has coefficient one at
every original source prime whose generic point maps to the centre.
All local parameters and original Rees charts are derived internally. -/
theorem exceptionalCartierDivisor_coefficient_eq_one
    {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (C : (sourceSurface X j q hclosed).PrimeCurve)
    (hcenter : (projection j q hclosed).base C.genericPoint = j.base q) :
    letI : IsIntegral (PointBlowupGluing.scheme j q hclosed) :=
      (sourceSurface X j q hclosed).integral
    (sourceSurface X j q hclosed).cartierToWeilHom
      (exceptionalCartierDivisor j q hclosed) C = 1 := by
  letI : IsIntegral (PointBlowupGluing.scheme j q hclosed) :=
    (sourceSurface X j q hclosed).integral
  obtain ⟨a, b, hspan, ha, hb, _⟩ := X.pointBlowup_snc_original_parameters j q hclosed
    (1 : Localization.AtPrime q.asIdeal) (Or.inl isUnit_one)
  obtain ⟨d, hd, P, hP⟩ := exists_original_parameter_chart_at_center j q hclosed a b
    hspan C.genericPoint hcenter
  rcases hd with hda | hdb
  · subst d
    exact exceptionalCartierDivisor_coefficient_eq_one_of_chart X j q hclosed C a P hP
      hcenter (centerParameter q b) ha hb hspan.symm
  · subst d
    let e := openImmersionStalkLocalizationEquiv j q
    have hR : RegularLocal (Localization.AtPrime q.asIdeal) :=
      regularLocal_of_ringEquiv e (X.regularPoints_of_isSmooth (j.base q))
    have hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 2 :=
      (ringKrullDim_eq_of_ringEquiv e).symm.trans
        (X.closed_stalk_dimension_two (j.base q) hclosed)
    have hmax : centerIdeal q = maximalIdeal (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal)
    have hswap : Ideal.span
        {algebraMap R (Localization.AtPrime q.asIdeal) (b : R),
          algebraMap R (Localization.AtPrime q.asIdeal) (a : R)} = centerIdeal q := by
      rw [Set.pair_comm]
      exact hspan
    have hpair := RegularLocalTwoParameters.regular_pair hR hdim
      (algebraMap R (Localization.AtPrime q.asIdeal) (b : R))
      (algebraMap R (Localization.AtPrime q.asIdeal) (a : R)) (hswap.trans hmax)
    exact exceptionalCartierDivisor_coefficient_eq_one_of_chart X j q hclosed C b P hP
      hcenter (centerParameter q a) hpair.1 hpair.2 hswap.symm

end KltDP.Geometry.PointBlowupExceptionalPrimeStalk

#check @KltDP.Geometry.PointBlowupExceptionalPrimeStalk.exceptionalCartierDivisor_coefficient_eq_one
#print axioms KltDP.Geometry.PointBlowupExceptionalPrimeStalk.exceptionalCartierDivisor_coefficient_eq_one
