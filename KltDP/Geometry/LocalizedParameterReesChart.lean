import KltDP.Geometry.LocalizedParameterNumerator
import KltDP.Geometry.ReesChartUnitRescaling
import KltDP.Geometry.AffineBlowupChartBaseChangeMap

/-!
# A given local parameter chart and its original numerator chart

The centre stays literally the image of the original prime ideal in its
localization. A numerator and unit denominator are derived for the given
element of that ideal, and the original unit-rescaling equivalence then
compares the two actual Rees charts. Both coefficient maps and the native
fractions are retained; no comparison equation or isomorphism is assumed.
-/

noncomputable section

namespace KltDP.Geometry.LocalizedParameterReesChart

open AffineBlowup AffineBlowupChartBaseChange

universe u

variable {R : Type u} [CommRing R] (m : Ideal R) [m.IsPrime]

/-- The actual centre ideal appearing in the original base-change chart. -/
abbrev localCenter := m.map (algebraMap R (Localization.AtPrime m))

private theorem numerator_exists (f : localCenter m) :
    ∃ r : m, ∃ v : (Localization.AtPrime m)ˣ,
      algebraMap R (Localization.AtPrime m) (r : R) =
        (v : Localization.AtPrime m) * (f : Localization.AtPrime m) := by
  have hf : (f : Localization.AtPrime m) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := m)]
    exact f.property
  exact LocalizedParameterNumerator.exists_original_numerator m ⟨f, hf⟩

/-- The original numerator chosen from the proved localization representation. -/
def originalNumerator (f : localCenter m) : m :=
  Classical.choose (numerator_exists m f)

/-- The actual denominator unit in the original centre localization. -/
def denominatorUnit (f : localCenter m) : (Localization.AtPrime m)ˣ :=
  Classical.choose (Classical.choose_spec (numerator_exists m f))

/-- The numerator as the literal element used in the original base-change chart. -/
def mappedNumerator (f : localCenter m) : localCenter m :=
  mappedElement m (algebraMap R (Localization.AtPrime m)) (originalNumerator m f)

theorem mappedNumerator_eq (f : localCenter m) :
    (mappedNumerator m f : Localization.AtPrime m) =
      (denominatorUnit m f : Localization.AtPrime m) * (f : Localization.AtPrime m) :=
  Classical.choose_spec (Classical.choose_spec (numerator_exists m f))

/-- The actual map from the given parameter chart to its original numerator chart. -/
def chartEquiv (f : localCenter m) :
    chartRing (localCenter m) f ≃+* chartRing (localCenter m) (mappedNumerator m f) :=
  chartUnitMultipleEquiv (localCenter m) f (mappedNumerator m f)
    (denominatorUnit m f) (mappedNumerator_eq m f)

theorem chartEquiv_baseMap (f : localCenter m) (r : Localization.AtPrime m) :
    chartEquiv m f (chartBaseMap (localCenter m) f r) =
      chartBaseMap (localCenter m) (mappedNumerator m f) r :=
  chartUnitMultipleEquiv_baseMap (localCenter m) f (mappedNumerator m f)
    (denominatorUnit m f) (mappedNumerator_eq m f) r

theorem chartEquiv_fraction (f b : localCenter m) :
    chartEquiv m f (chartFraction (localCenter m) f b) =
      chartBaseMap (localCenter m) (mappedNumerator m f)
          (denominatorUnit m f : Localization.AtPrime m) *
        chartFraction (localCenter m) (mappedNumerator m f) b :=
  chartUnitMultipleEquiv_fraction (localCenter m) f (mappedNumerator m f)
    (denominatorUnit m f) (mappedNumerator_eq m f) b

theorem chartEquiv_symm_fraction (f b : localCenter m) :
    (chartEquiv m f).symm (chartFraction (localCenter m) (mappedNumerator m f) b) =
      chartBaseMap (localCenter m) f
          ((denominatorUnit m f)⁻¹ : (Localization.AtPrime m)ˣ) *
        chartFraction (localCenter m) f b :=
  chartUnitMultipleEquiv_symm_fraction (localCenter m) f (mappedNumerator m f)
    (denominatorUnit m f) (mappedNumerator_eq m f) b

end KltDP.Geometry.LocalizedParameterReesChart
