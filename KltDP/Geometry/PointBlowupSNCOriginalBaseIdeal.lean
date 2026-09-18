import KltDP.Geometry.PointBlowupSNCLocalizedReducedIdeal
import KltDP.Geometry.AffineBlowupChartStalkBaseIdeals
import KltDP.Geometry.AffineBlowupChartLocalizationCenter

/-!
# The original reduced boundary from its actual localized base ideal

The fixed original source chart need not make the boundary globally
principal. Its actual affine ideal is only normalized in the original
centre localization. The resulting reduced ideal on the original Rees
chart has an SNC generator at every original point above that centre.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open AffineBlowup AffineBlowupChartBaseChange LocalizedParameterReesChart

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
variable {R : Type u} [CommRing R]
variable (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]

/-- An SNC generator of the actual localized base ideal produces an SNC
generator of the original reduced pulled ideal on every original chart. -/
theorem pointBlowup_snc_original_base_ideal
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (J : Ideal R) (c : Localization.AtPrime q.asIdeal)
    (hJ : Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) J = Ideal.span {c})
    (hc : IsStrictNormalCrossingsEquation (Localization.AtPrime q.asIdeal) c)
    (a : q.asIdeal) (P : Ideal (chartRing q.asIdeal a)) [P.IsPrime]
    (hPq : P.comap (chartBaseMap q.asIdeal a) = q.asIdeal) :
    ∃ t : Localization.AtPrime P,
      Ideal.map (algebraMap (chartRing q.asIdeal a) (Localization.AtPrime P))
        (chartCenterIdeal q.asIdeal a * Ideal.map (chartBaseMap q.asIdeal a) J).radical =
        Ideal.span {t} ∧ IsStrictNormalCrossingsEquation (Localization.AtPrime P) t := by
  let Q := localizedChartPrime q.asIdeal a q.asIdeal P hPq
  let d := mappedElement q.asIdeal (algebraMap R (Localization.AtPrime q.asIdeal)) a
  have hcenter : chartCenterIdeal (localCenter q.asIdeal) d ≤ Q :=
    localizedChartPrime_center_le q.asIdeal a P hPq
  obtain ⟨t, ht, hsnc⟩ := X.pointBlowup_snc_localized_reduced_ideal j q hclosed c hc d Q hcenter
  let ε := originalChartStalkEquiv q.asIdeal a q.asIdeal P hPq
  refine ⟨ε.symm t, ?_, hsnc.map_equiv ε.symm⟩
  have htransport := originalChartStalkEquiv_reducedBaseIdeal q.asIdeal a q.asIdeal P hPq J
  rw [hJ] at htransport
  have heq : Ideal.map ε.toRingHom
      (Ideal.map (algebraMap (chartRing q.asIdeal a) (Localization.AtPrime P))
        (chartCenterIdeal q.asIdeal a * Ideal.map (chartBaseMap q.asIdeal a) J).radical) =
      Ideal.span {t} := htransport.trans ht
  have hback := congrArg (Ideal.map ε.symm.toRingHom) heq
  rw [Ideal.map_map ε.toRingHom ε.symm.toRingHom,
    RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id] at hback
  simpa only [Ideal.map_span, Set.image_singleton] using hback

end KltDP.Geometry.NormalProjectiveSurface
