import KltDP.Geometry.LocalizedParameterReesChart
import Mathlib.RingTheory.Localization.Basic

/-!
# The actual stalk map from a parameter chart to its numerator chart

The original parameter-chart prime determines its numerator-chart prime
through the already constructed chart equivalence. The pinned localization
equivalence then gives the actual stalk comparison, including its action
on base coefficients and the original Rees fraction.
-/

noncomputable section

namespace KltDP.Geometry.LocalizedParameterReesChart

open AffineBlowup

universe u

variable {R : Type u} [CommRing R] (m : Ideal R) [m.IsPrime]
variable (f : localCenter m)
variable (P : Ideal (chartRing (localCenter m) f)) [P.IsPrime]

/-- The actual prime corresponding under the original unit-rescaled chart map. -/
def numeratorPrime : Ideal (chartRing (localCenter m) (mappedNumerator m f)) :=
  P.comap (chartEquiv m f).symm

instance numeratorPrime_isPrime : (numeratorPrime m f P).IsPrime := by
  dsimp only [numeratorPrime]
  infer_instance

instance numeratorPrime_isMaximal [P.IsMaximal] :
    (numeratorPrime m f P).IsMaximal := by
  dsimp only [numeratorPrime]
  infer_instance

private theorem chartEquiv_symm_baseMap (r : Localization.AtPrime m) :
    (chartEquiv m f).symm (chartBaseMap (localCenter m) (mappedNumerator m f) r) =
      chartBaseMap (localCenter m) f r :=
  chartUnitMultipleEquiv_symm_baseMap (localCenter m) f (mappedNumerator m f)
    (denominatorUnit m f) (mappedNumerator_eq m f) r

/-- The original centre image of the given point is preserved by the chart equivalence. -/
theorem numeratorPrime_comap_baseMap :
    (numeratorPrime m f P).comap (chartBaseMap (localCenter m) (mappedNumerator m f)) =
      P.comap (chartBaseMap (localCenter m) f) := by
  ext r
  change (chartEquiv m f).symm
      (chartBaseMap (localCenter m) (mappedNumerator m f) r) ∈ P ↔
    chartBaseMap (localCenter m) f r ∈ P
  rw [chartEquiv_symm_baseMap]

private theorem chartEquiv_map_primeCompl :
    P.primeCompl.map (chartEquiv m f).toMonoidHom =
      (numeratorPrime m f P).primeCompl := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (chartEquiv m f).symm (chartEquiv m f x) ∉ P
    simpa only [RingEquiv.symm_apply_apply] using hx
  · intro hz
    refine ⟨(chartEquiv m f).symm z, ?_, (chartEquiv m f).apply_symm_apply z⟩
    exact hz

/-- The pinned localization map of the actual parameter-to-numerator chart map. -/
def stalkEquiv :
    Localization.AtPrime P ≃+* Localization.AtPrime (numeratorPrime m f P) :=
  IsLocalization.ringEquivOfRingEquiv
    (M := P.primeCompl) (T := (numeratorPrime m f P).primeCompl)
    (Localization.AtPrime P) (Localization.AtPrime (numeratorPrime m f P))
    (chartEquiv m f) (chartEquiv_map_primeCompl m f P)

theorem stalkEquiv_to_map (z : chartRing (localCenter m) f) :
    stalkEquiv m f P (algebraMap _ (Localization.AtPrime P) z) =
      algebraMap _ (Localization.AtPrime (numeratorPrime m f P)) (chartEquiv m f z) :=
  IsLocalization.ringEquivOfRingEquiv_eq (chartEquiv_map_primeCompl m f P) z

theorem stalkEquiv_baseMap (r : Localization.AtPrime m) :
    stalkEquiv m f P
        (algebraMap _ (Localization.AtPrime P) (chartBaseMap (localCenter m) f r)) =
      algebraMap _ (Localization.AtPrime (numeratorPrime m f P))
        (chartBaseMap (localCenter m) (mappedNumerator m f) r) := by
  rw [stalkEquiv_to_map, chartEquiv_baseMap]

theorem stalkEquiv_fraction (b : localCenter m) :
    stalkEquiv m f P
        (algebraMap _ (Localization.AtPrime P) (chartFraction (localCenter m) f b)) =
      algebraMap _ (Localization.AtPrime (numeratorPrime m f P))
          (chartBaseMap (localCenter m) (mappedNumerator m f)
            (denominatorUnit m f : Localization.AtPrime m)) *
        algebraMap _ (Localization.AtPrime (numeratorPrime m f P))
          (chartFraction (localCenter m) (mappedNumerator m f) b) := by
  rw [stalkEquiv_to_map, chartEquiv_fraction, map_mul]

end KltDP.Geometry.LocalizedParameterReesChart
