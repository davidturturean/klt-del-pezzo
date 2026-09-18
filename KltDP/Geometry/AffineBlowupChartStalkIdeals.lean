import KltDP.Geometry.AffineBlowupChartStalkAtCenter
import KltDP.Geometry.AffineBlowupConormal
import Mathlib.RingTheory.Localization.Ideal

/-!
# Original reduced chart ideals after localization of the base

The already constructed original chart-stalk equivalence is induced by
the actual Rees base-change map. Its coefficient formula transports all
chart ideals, and localization compatibility with radicals transports
the actual reduced exceptional-plus-pullback ideal.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupChartBaseChange

open AffineBlowup

universe u

private theorem map_radical_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (J : Ideal A) :
    Ideal.map e.toRingHom J.radical = (Ideal.map e.toRingHom J).radical := by
  calc
    _ = J.radical.comap e.symm := Ideal.map_comap_of_equiv e
    _ = (J.comap e.symm).radical := Ideal.comap_radical e.symm J
    _ = _ := congrArg Ideal.radical (Ideal.map_comap_of_equiv e).symm

variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
variable (m : Ideal R) [m.IsPrime] (P : Ideal (chartRing I a)) [P.IsPrime]
variable (hPm : P.comap (chartBaseMap I a) = m)

/-- The literal original chart-stalk equivalence transports any chart ideal. -/
theorem originalChartStalkEquiv_ideal (J : Ideal (chartRing I a)) :
    Ideal.map (originalChartStalkEquiv I a m P hPm).toRingHom
      (Ideal.map (algebraMap (chartRing I a) (Localization.AtPrime P)) J) =
      Ideal.map (algebraMap _ (Localization.AtPrime (localizedChartPrime I a m P hPm)))
        (Ideal.map (chartMap I (algebraMap R (Localization.AtPrime m)) a) J) := by
  have hmap : (originalChartStalkEquiv I a m P hPm).toRingHom.comp
      (algebraMap (chartRing I a) (Localization.AtPrime P)) =
      (algebraMap _ (Localization.AtPrime (localizedChartPrime I a m P hPm))).comp
        (chartMap I (algebraMap R (Localization.AtPrime m)) a) := by
    apply RingHom.ext
    intro z
    exact originalChartStalkEquiv_to_map I a m P hPm z
  simpa only [Ideal.map_map] using congrArg (fun f => Ideal.map f J) hmap

/-- Localization and the actual chart-stalk equivalence preserve the
radical of every original extended chart ideal. -/
theorem originalChartStalkEquiv_radicalIdeal (J : Ideal (chartRing I a)) :
    Ideal.map (originalChartStalkEquiv I a m P hPm).toRingHom
      (Ideal.map (algebraMap (chartRing I a) (Localization.AtPrime P)) J.radical) =
      Ideal.map (algebraMap _ (Localization.AtPrime (localizedChartPrime I a m P hPm)))
        (Ideal.map (chartMap I (algebraMap R (Localization.AtPrime m)) a) J).radical := by
  rw [IsLocalization.map_radical P.primeCompl (Localization.AtPrime P),
    IsLocalization.map_radical (localizedChartPrime I a m P hPm).primeCompl
      (Localization.AtPrime (localizedChartPrime I a m P hPm)),
    map_radical_ringEquiv, originalChartStalkEquiv_ideal]

/-- The original chart map preserves every ideal extended from the base. -/
theorem chartMap_baseIdeal (J : Ideal R) :
    Ideal.map (chartMap I (algebraMap R (Localization.AtPrime m)) a)
      (Ideal.map (chartBaseMap I a) J) =
      Ideal.map (chartBaseMap (I.map (algebraMap R (Localization.AtPrime m)))
        (mappedElement I (algebraMap R (Localization.AtPrime m)) a))
        (Ideal.map (algebraMap R (Localization.AtPrime m)) J) := by
  have hmap : (chartMap I (algebraMap R (Localization.AtPrime m)) a).comp
      (chartBaseMap I a) =
      (chartBaseMap (I.map (algebraMap R (Localization.AtPrime m)))
        (mappedElement I (algebraMap R (Localization.AtPrime m)) a)).comp
        (algebraMap R (Localization.AtPrime m)) := by
    apply RingHom.ext
    intro r
    exact chartMap_baseMap I (algebraMap R (Localization.AtPrime m)) a r
  simpa only [Ideal.map_map] using congrArg (fun f => Ideal.map f J) hmap

/-- The localized original reduced boundary ideal is exactly the reduced
boundary ideal on the original localized-base chart. -/
theorem originalChartStalkEquiv_reducedBoundaryIdeal (c : R) :
    Ideal.map (originalChartStalkEquiv I a m P hPm).toRingHom
      (Ideal.map (algebraMap (chartRing I a) (Localization.AtPrime P))
        (chartCenterIdeal I a * Ideal.map (chartBaseMap I a) (Ideal.span {c})).radical) =
      Ideal.map (algebraMap _ (Localization.AtPrime (localizedChartPrime I a m P hPm)))
        (chartCenterIdeal (I.map (algebraMap R (Localization.AtPrime m)))
          (mappedElement I (algebraMap R (Localization.AtPrime m)) a) *
        Ideal.map (chartBaseMap (I.map (algebraMap R (Localization.AtPrime m)))
          (mappedElement I (algebraMap R (Localization.AtPrime m)) a))
          (Ideal.span {algebraMap R (Localization.AtPrime m) c})).radical := by
  rw [originalChartStalkEquiv_radicalIdeal]
  simp only [chartCenterIdeal, Ideal.map_mul, chartMap_baseIdeal,
    Ideal.map_span, Set.image_singleton, chartMap_baseMap, baseMap, RingHom.comp_apply]

end KltDP.Geometry.AffineBlowupChartBaseChange
