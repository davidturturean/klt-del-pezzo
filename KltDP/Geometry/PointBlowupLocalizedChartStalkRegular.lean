import KltDP.Geometry.PointBlowupChartStalkRegular
import KltDP.Geometry.AffineBlowupChartLocalizationClosedPoint

/-! Original smooth point-blowup regularity on the chart over its original centre stalk. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open AffineBlowup AffineBlowupChartBaseChange

/-- Regularity and dimension two are derived on the localized chart's actual
stalk by its proved comparison with the original glued blowup stalk. -/
theorem pointBlowup_localized_chart_stalk_regular_dimension
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ X.toScheme)
    [IsOpenImmersion j] (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme)) (a : q.asIdeal)
    (P : Ideal (chartRing q.asIdeal a)) [P.IsMaximal]
    (hPq : P.comap (chartBaseMap q.asIdeal a) = q.asIdeal) :
    RegularLocal (Localization.AtPrime (localizedChartPrime q.asIdeal a q.asIdeal P hPq)) ∧
      ringKrullDim (Localization.AtPrime (localizedChartPrime q.asIdeal a q.asIdeal P hPq)) = 2 := by
  have h := X.pointBlowup_chart_stalk_regular_dimension j q hclosed a P
  let e := originalChartStalkEquiv q.asIdeal a q.asIdeal P hPq
  exact ⟨regularLocal_of_ringEquiv e h.1,
    (ringKrullDim_eq_of_ringEquiv e).symm.trans h.2⟩

end KltDP.Geometry.NormalProjectiveSurface
