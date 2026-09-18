import KltDP.Geometry.AffineBlowupChartStalkIdeals

/-!
# Actual base ideals in the reduced blowup boundary

The base ideal can be locally principal at the centre without being
principal on the original affine chart. Its original ideal and extension
are retained in the actual chart-stalk comparison.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupChartBaseChange

open AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
variable (m : Ideal R) [m.IsPrime] (P : Ideal (chartRing I a)) [P.IsPrime]
variable (hPm : P.comap (chartBaseMap I a) = m)

/-- Preserve the original reduced exceptional-plus-pulled base ideal,
without imposing global principality on that original affine ideal. -/
theorem originalChartStalkEquiv_reducedBaseIdeal (J : Ideal R) :
    Ideal.map (originalChartStalkEquiv I a m P hPm).toRingHom
      (Ideal.map (algebraMap (chartRing I a) (Localization.AtPrime P))
        (chartCenterIdeal I a * Ideal.map (chartBaseMap I a) J).radical) =
      Ideal.map (algebraMap _ (Localization.AtPrime (localizedChartPrime I a m P hPm)))
        (chartCenterIdeal (I.map (algebraMap R (Localization.AtPrime m)))
          (mappedElement I (algebraMap R (Localization.AtPrime m)) a) *
        Ideal.map (chartBaseMap (I.map (algebraMap R (Localization.AtPrime m)))
          (mappedElement I (algebraMap R (Localization.AtPrime m)) a))
          (Ideal.map (algebraMap R (Localization.AtPrime m)) J)).radical := by
  rw [originalChartStalkEquiv_radicalIdeal]
  simp only [chartCenterIdeal, Ideal.map_mul, chartMap_baseIdeal]

end KltDP.Geometry.AffineBlowupChartBaseChange
