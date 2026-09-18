import KltDP.Geometry.LocalizedParameterReesStalk
import KltDP.Geometry.PointBlowupLocalizedClosedChartRegular

/-!
# Original smooth blowup geometry on a given local parameter chart

The given parameter is related to an original numerator by a derived unit.
Its original chart point is carried through that exact chart equivalence.
The proved localized numerator-chart geometry then supplies regularity and
dimension two on the original parameter-chart stalk, with no regularity,
dimension, maximal-comap, or point-correspondence premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open AffineBlowup LocalizedParameterReesChart

/-- Every actual closed parameter-chart point over the original centre has
the regular two-dimensional local ring of the original smooth point blowup. -/
theorem pointBlowup_parameter_chart_stalk_regular_dimension
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ X.toScheme)
    [IsOpenImmersion j] (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (f : localCenter q.asIdeal)
    (P : Ideal (chartRing (localCenter q.asIdeal) f)) [P.IsMaximal]
    (hcenter : chartCenterIdeal (localCenter q.asIdeal) f ≤ P) :
    RegularLocal (Localization.AtPrime P) ∧ ringKrullDim (Localization.AtPrime P) = 2 := by
  let Q := numeratorPrime q.asIdeal f P
  letI : Q.IsMaximal := by dsimp only [Q]; infer_instance
  have hQcenter : chartCenterIdeal (localCenter q.asIdeal)
      (mappedNumerator q.asIdeal f) ≤ Q := by
    apply Ideal.map_le_iff_le_comap.mpr
    change localCenter q.asIdeal ≤ (numeratorPrime q.asIdeal f P).comap
      (chartBaseMap (localCenter q.asIdeal) (mappedNumerator q.asIdeal f))
    rw [numeratorPrime_comap_baseMap]
    exact Ideal.map_le_iff_le_comap.mp hcenter
  have h := X.pointBlowup_localized_closed_chart_stalk_regular_dimension j q hclosed
    (originalNumerator q.asIdeal f) Q hQcenter
  let e := stalkEquiv q.asIdeal f P
  exact ⟨regularLocal_of_ringEquiv e.symm h.1,
    (ringKrullDim_eq_of_ringEquiv e.symm).symm.trans h.2⟩

end KltDP.Geometry.NormalProjectiveSurface
