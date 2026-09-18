import KltDP.Geometry.PointBlowupParameterChartAllSNC
import KltDP.Geometry.RegularSurfaceBlowupReducedEquations

/-!
# The actual reduced pulled boundary has an SNC chart equation

The coefficient is the original local boundary equation, including its
original unit. Each possible branch expression is normalized by the
proved actual ideal equalities. A single equation for the whole reduced
chart ideal is then SNC at every chart prime above the centre. The
exceptional component is included in the reduced boundary throughout.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open AffineBlowup AffineBlowupRegularPairChart LocalizedParameterReesChart

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
variable {R : Type u} [CommRing R]
variable (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]

/-- An actual boundary-adapted parameter pair gives a literal generator
of the original reduced pulled ideal, SNC at all points over the centre. -/
theorem pointBlowup_reduced_boundary_chart_snc
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (f g : localCenter q.asIdeal)
    (hfg : Ideal.span {(f : Localization.AtPrime q.asIdeal),
      (g : Localization.AtPrime q.asIdeal)} = localCenter q.asIdeal)
    (c : Localization.AtPrime q.asIdeal)
    (hc : IsUnit c ∨ ∃ v : (Localization.AtPrime q.asIdeal)ˣ,
      c = (v : Localization.AtPrime q.asIdeal) * (f : Localization.AtPrime q.asIdeal) ∨
      c = (v : Localization.AtPrime q.asIdeal) * (g : Localization.AtPrime q.asIdeal) ∨
      c = (v : Localization.AtPrime q.asIdeal) *
        ((f : Localization.AtPrime q.asIdeal) * (g : Localization.AtPrime q.asIdeal))) :
    ∃ e : chartRing (localCenter q.asIdeal) f,
      (chartCenterIdeal (localCenter q.asIdeal) f *
        Ideal.map (chartBaseMap (localCenter q.asIdeal) f) (Ideal.span {c})).radical =
        Ideal.span {e} ∧
      ∀ (P : Ideal (chartRing (localCenter q.asIdeal) f)) [P.IsPrime],
        chartCenterIdeal (localCenter q.asIdeal) f ≤ P →
        IsStrictNormalCrossingsEquation (Localization.AtPrime P)
          (algebraMap (chartRing (localCenter q.asIdeal) f) (Localization.AtPrime P) e) := by
  have hmax : localCenter q.asIdeal = maximalIdeal (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal)
  let ε := openImmersionStalkLocalizationEquiv j q
  have hA : RegularLocal (Localization.AtPrime q.asIdeal) :=
    regularLocal_of_ringEquiv ε (X.regularPoints_of_isSmooth (j.base q))
  have hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 2 :=
    (ringKrullDim_eq_of_ringEquiv ε).symm.trans
      (X.closed_stalk_dimension_two (j.base q) hclosed)
  rcases hc with hu | ⟨v, hfirst | hsecond | hpair⟩
  · refine ⟨chartBaseMap (localCenter q.asIdeal) f (f : Localization.AtPrime q.asIdeal),
      reduced_exceptional_unit_ideal (localCenter q.asIdeal) f g hA hdim hfg.symm hmax c hu, ?_⟩
    intro P hP hcenter
    exact (X.pointBlowup_parameter_chart_snc_over_center j q hclosed f g hfg P hcenter).1
  · refine ⟨chartBaseMap (localCenter q.asIdeal) f (f : Localization.AtPrime q.asIdeal), ?_, ?_⟩
    · rw [hfirst, reduced_exceptional_unit_mul_ideal]
      exact reduced_exceptional_first_ideal (localCenter q.asIdeal) f g hA hdim hfg.symm hmax
    · intro P hP hcenter
      exact (X.pointBlowup_parameter_chart_snc_over_center j q hclosed f g hfg P hcenter).1
  · refine ⟨chartBaseMap (localCenter q.asIdeal) f (f : Localization.AtPrime q.asIdeal) *
        chartFraction (localCenter q.asIdeal) f g, ?_, ?_⟩
    · rw [hsecond, reduced_exceptional_unit_mul_ideal]
      exact reduced_exceptional_second_ideal (localCenter q.asIdeal) f g hA hdim hfg.symm hmax
    · intro P hP hcenter
      exact (X.pointBlowup_parameter_chart_snc_over_center j q hclosed f g hfg P hcenter).2.2
  · refine ⟨chartBaseMap (localCenter q.asIdeal) f (f : Localization.AtPrime q.asIdeal) *
        chartFraction (localCenter q.asIdeal) f g, ?_, ?_⟩
    · rw [hpair, reduced_exceptional_unit_mul_ideal]
      exact reduced_exceptional_pair_ideal (localCenter q.asIdeal) f g hA hdim hfg.symm hmax
    · intro P hP hcenter
      exact (X.pointBlowup_parameter_chart_snc_over_center j q hclosed f g hfg P hcenter).2.2

end KltDP.Geometry.NormalProjectiveSurface
