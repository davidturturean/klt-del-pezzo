import KltDP.Geometry.PointBlowupParameterStalkRegular
import KltDP.Geometry.AffineBlowupRegularPairClosedSNC
import KltDP.Geometry.RegularLocalTwoParameters
import KltDP.Geometry.SmoothSurfaceRegularity
import KltDP.Compatibility.ClosedAlgebraResidue

/-!
# Actual closed-point SNC equations for given original surface parameters

The original smooth surface supplies regularity and dimension of its centre
stalk. Its original finite-type chart supplies the algebraically closed
centre residue field. The given maximal-ideal spanning pair then supplies
the regular-pair conditions. At every closed point of its actual Rees chart
over the centre, the exceptional equation, residual fraction and their
reduced product satisfy the shared SNC equation definition. No local
regularity, dimension, residue-field, or SNC conclusion is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open AffineBlowup AffineBlowupRegularPairChart LocalizedParameterReesChart

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : NormalProjectiveSurface k)
variable {R : Type u} [CommRing R]
variable (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]

private theorem parameterCenter_isMaximal : (localCenter q.asIdeal).IsMaximal := by
  rw [localCenter, Localization.AtPrime.map_eq_maximalIdeal]
  infer_instance

attribute [local instance] Ideal.Quotient.field

private theorem parameterCenter_isAlgClosed
    (Y : NormalProjectiveSurface k)
    (i : Spec (CommRingCat.of R) ⟶ Y.toScheme) [IsOpenImmersion i]
    (p : PrimeSpectrum R) [p.asIdeal.IsMaximal] [(localCenter p.asIdeal).IsMaximal] :
    IsAlgClosed (Localization.AtPrime p.asIdeal ⧸ localCenter p.asIdeal) := by
  letI := Y.affineChartAlgebra i
  letI := Y.affineChartAlgebra_finiteType i
  let e : k ≃+* (Localization.AtPrime p.asIdeal ⧸ localCenter p.asIdeal) :=
    (KltDP.Compatibility.closedResidueFieldAlgEquiv k p.asIdeal).toRingEquiv.trans
      (Ideal.quotEquivOfEq (Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)).symm)
  exact IsAlgClosed.of_ringEquiv k _ e

/-- The literal three reduced-support equations are SNC at every actual closed
chart point above the centre, for the given original surface parameter pair. -/
theorem pointBlowup_parameter_chart_snc_at_closed [IsSmooth X.structureMorphism]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (f g : localCenter q.asIdeal)
    (hfg : Ideal.span {(f : Localization.AtPrime q.asIdeal),
      (g : Localization.AtPrime q.asIdeal)} = localCenter q.asIdeal)
    (P : Ideal (chartRing (localCenter q.asIdeal) f)) [P.IsMaximal]
    (hcenter : chartCenterIdeal (localCenter q.asIdeal) f ≤ P) :
    let ψ := algebraMap (chartRing (localCenter q.asIdeal) f) (Localization.AtPrime P)
    IsStrictNormalCrossingsEquation (Localization.AtPrime P)
        (ψ (chartBaseMap (localCenter q.asIdeal) f (f : Localization.AtPrime q.asIdeal))) ∧
      IsStrictNormalCrossingsEquation (Localization.AtPrime P)
        (ψ (chartFraction (localCenter q.asIdeal) f g)) ∧
      IsStrictNormalCrossingsEquation (Localization.AtPrime P)
        (ψ (chartBaseMap (localCenter q.asIdeal) f (f : Localization.AtPrime q.asIdeal) *
          chartFraction (localCenter q.asIdeal) f g)) := by
  letI : (localCenter q.asIdeal).IsMaximal := parameterCenter_isMaximal q
  letI : IsAlgClosed (Localization.AtPrime q.asIdeal ⧸ localCenter q.asIdeal) :=
    parameterCenter_isAlgClosed X j q
  let e := openImmersionStalkLocalizationEquiv j q
  have hR : RegularLocal (Localization.AtPrime q.asIdeal) :=
    regularLocal_of_ringEquiv e (X.regularPoints_of_isSmooth (j.base q))
  have hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 2 :=
    (ringKrullDim_eq_of_ringEquiv e).symm.trans
      (X.closed_stalk_dimension_two (j.base q) hclosed)
  have hspan := hfg.trans (Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal))
  have hpair := RegularLocalTwoParameters.regular_pair hR hdim
    (f : Localization.AtPrime q.asIdeal) (g : Localization.AtPrime q.asIdeal) hspan
  have hlocal := X.pointBlowup_parameter_chart_stalk_regular_dimension j q hclosed f P hcenter
  exact ⟨exceptional_snc_at_closed (localCenter q.asIdeal) f g hpair.1 hpair.2 hfg.symm
      P hcenter hlocal.1 hlocal.2,
    fraction_snc_at_closed (localCenter q.asIdeal) f g hpair.1 hpair.2 hfg.symm
      P hcenter hlocal.1 hlocal.2,
    exceptional_fraction_snc_at_closed (localCenter q.asIdeal) f g hpair.1 hpair.2 hfg.symm
      P hcenter hlocal.1 hlocal.2⟩

end KltDP.Geometry.NormalProjectiveSurface
