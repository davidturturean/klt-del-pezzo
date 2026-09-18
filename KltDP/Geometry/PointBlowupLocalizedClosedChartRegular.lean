import KltDP.Geometry.PointBlowupChartStalkRegular
import KltDP.Geometry.AffineBlowupChartLocalizationStalks
import KltDP.Geometry.AffineBlowupChartLocalizationMaximalComap

/-! Closed localized-chart stalks inherit the original smooth point-blowup geometry. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open AffineBlowup AffineBlowupChartBaseChange

/-- Starting with a closed point of the localized numerator chart over the
centre, both regularity and dimension two are derived from the original blowup.
The original chart prime is its actual comap and its maximality is proved. -/
theorem pointBlowup_localized_closed_chart_stalk_regular_dimension
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ X.toScheme)
    [IsOpenImmersion j] (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme)) (a : q.asIdeal)
    (Q : Ideal (chartRing (q.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)))
      (mappedElement q.asIdeal (algebraMap R (Localization.AtPrime q.asIdeal)) a))) [Q.IsMaximal]
    (hcenter : chartCenterIdeal (q.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)))
      (mappedElement q.asIdeal (algebraMap R (Localization.AtPrime q.asIdeal)) a) ≤ Q) :
    RegularLocal (Localization.AtPrime Q) ∧ ringKrullDim (Localization.AtPrime Q) = 2 := by
  let P := Q.comap (chartMap q.asIdeal (algebraMap R (Localization.AtPrime q.asIdeal)) a)
  letI : P.IsMaximal := localization_comap_isMaximal_of_center q.asIdeal a Q hcenter
  have h := X.pointBlowup_chart_stalk_regular_dimension j q hclosed a P
  let e := localizationLocalRingEquiv q.asIdeal q.asIdeal.primeCompl a Q
  exact ⟨regularLocal_of_ringEquiv e h.1,
    (ringKrullDim_eq_of_ringEquiv e).symm.trans h.2⟩

end KltDP.Geometry.NormalProjectiveSurface
