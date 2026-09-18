import KltDP.Geometry.PointBlowupSNCReducedChartCover
import KltDP.Geometry.AffineBlowupParameterChartIdeals
import KltDP.Geometry.StrictNormalCrossingsEquiv

/-!
# The original localized reduced boundary ideal at every exceptional point

An arbitrary original Rees chart point is moved to one of the two
boundary-adapted charts through their actual common scheme point. The
original stalk equivalence transports both the derived ideal generator
and its SNC parameter system back to the given chart.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open AffineBlowup LocalizedParameterReesChart

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
variable {R : Type u} [CommRing R]
variable (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]

/-- The actual reduced ideal has an SNC generator in the local ring of
every original localized Rees chart point above the original centre. -/
theorem pointBlowup_snc_localized_reduced_ideal
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (c : Localization.AtPrime q.asIdeal)
    (hc : IsStrictNormalCrossingsEquation (Localization.AtPrime q.asIdeal) c)
    (a : localCenter q.asIdeal)
    (P : Ideal (chartRing (localCenter q.asIdeal) a)) [P.IsPrime]
    (hcenter : chartCenterIdeal (localCenter q.asIdeal) a ≤ P) :
    ∃ t : Localization.AtPrime P,
      Ideal.map (algebraMap (chartRing (localCenter q.asIdeal) a) (Localization.AtPrime P))
        (chartCenterIdeal (localCenter q.asIdeal) a *
          Ideal.map (chartBaseMap (localCenter q.asIdeal) a) (Ideal.span {c})).radical =
        Ideal.span {t} ∧ IsStrictNormalCrossingsEquation (Localization.AtPrime P) t := by
  obtain ⟨f, g, hfg, _, hequations⟩ :=
    X.pointBlowup_snc_reduced_chart_cover j q hclosed c hc
  let p : PrimeSpectrum (chartRing (localCenter q.asIdeal) a) := ⟨P, inferInstance⟩
  obtain ⟨d, hd, s, hs⟩ := exists_parameter_chart_point
    (localCenter q.asIdeal) f g hfg ((chartι (localCenter q.asIdeal) a).base p)
  have hscenter : chartCenterIdeal (localCenter q.asIdeal) d ≤ s.asIdeal :=
    chartPoint_center_of_eq (localCenter q.asIdeal) a d p s hs.symm hcenter
  obtain ⟨e, he, hsnc⟩ := hequations d hd
  let ε := parameterChartStalkEquiv (localCenter q.asIdeal) d a s p hs
  refine ⟨ε (algebraMap (chartRing (localCenter q.asIdeal) d)
    (Localization.AtPrime s.asIdeal) e), ?_, ?_⟩
  · have hideal := parameterChartStalkEquiv_reducedBoundaryIdeal
      (localCenter q.asIdeal) d a s p hs c
    rw [he] at hideal
    simp only [Ideal.map_span, Set.image_singleton] at hideal
    simpa only [Ideal.map_span, Set.image_singleton] using hideal.symm
  · exact (hsnc s.asIdeal hscenter).map_equiv ε

end KltDP.Geometry.NormalProjectiveSurface
