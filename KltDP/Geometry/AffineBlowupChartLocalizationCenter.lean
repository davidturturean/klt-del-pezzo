import KltDP.Geometry.AffineBlowupChartLocalizationPoint
import KltDP.Geometry.AffineBlowupConormal

/-! The constructed localized-chart point lies over the original centre stalk's closed point. -/

noncomputable section

namespace KltDP.Geometry.AffineBlowupChartBaseChange

open AffineBlowup

universe u

variable {R : Type u} [CommRing R]

/-- The actual localized base map sends the constructed point to the maximal
ideal of the original centre localization. -/
theorem localizedChartPrime_comap_baseMap (I : Ideal R) (a : I)
    (m : Ideal R) [m.IsPrime] (P : Ideal (chartRing I a)) [P.IsPrime]
    (hPm : P.comap (chartBaseMap I a) = m) :
    (localizedChartPrime I a m P hPm).comap
      (chartBaseMap (I.map (algebraMap R (Localization.AtPrime m)))
        (mappedElement I (algebraMap R (Localization.AtPrime m)) a)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
  let Q := localizedChartPrime I a m P hPm
  let β := chartBaseMap (I.map (algebraMap R (Localization.AtPrime m)))
    (mappedElement I (algebraMap R (Localization.AtPrime m)) a)
  have heq : (chartMap I (algebraMap R (Localization.AtPrime m)) a).comp
      (chartBaseMap I a) = β.comp (algebraMap R (Localization.AtPrime m)) := by
    apply RingHom.ext
    intro r
    exact chartMap_baseMap I (algebraMap R (Localization.AtPrime m)) a r
  have hbase : (Q.comap β).comap (algebraMap R (Localization.AtPrime m)) = m := by
    rw [Ideal.comap_comap, ← heq, ← Ideal.comap_comap]
    change ((localizedChartPrime I a m P hPm).comap
      (chartMap I (algebraMap R (Localization.AtPrime m)) a)).comap (chartBaseMap I a) = m
    rw [localizedChartPrime_comap]
    exact hPm
  change Q.comap β = _
  calc
    Q.comap β = ((Q.comap β).comap (algebraMap R (Localization.AtPrime m))).map
        (algebraMap R (Localization.AtPrime m)) :=
      (IsLocalization.map_comap m.primeCompl (Localization.AtPrime m) (Q.comap β)).symm
    _ = m.map (algebraMap R (Localization.AtPrime m)) := by rw [hbase]
    _ = _ := Localization.AtPrime.map_eq_maximalIdeal

/-- For the point-centre ideal itself, the constructed localized-chart point
contains the original exceptional chart ideal. -/
theorem localizedChartPrime_center_le (m : Ideal R) [m.IsPrime] (a : m)
    (P : Ideal (chartRing m a)) [P.IsPrime] (hPm : P.comap (chartBaseMap m a) = m) :
    chartCenterIdeal (m.map (algebraMap R (Localization.AtPrime m)))
      (mappedElement m (algebraMap R (Localization.AtPrime m)) a) ≤
        localizedChartPrime m a m P hPm := by
  change (m.map (algebraMap R (Localization.AtPrime m))).map
    (chartBaseMap (m.map (algebraMap R (Localization.AtPrime m)))
      (mappedElement m (algebraMap R (Localization.AtPrime m)) a)) ≤ _
  rw [Ideal.map_le_iff_le_comap, localizedChartPrime_comap_baseMap]
  exact (Localization.AtPrime.map_eq_maximalIdeal (I := m)).le

end KltDP.Geometry.AffineBlowupChartBaseChange
