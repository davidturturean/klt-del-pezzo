import KltDP.Geometry.AffineBlowupChartLocalizationPoint

/-! Stalk comparison at a specified original Rees-chart prime over the centre. -/

noncomputable section

namespace KltDP.Geometry.AffineBlowupChartBaseChange

open AffineBlowup

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

theorem localization_localRingHom_bijective_of_comap (I : Ideal R)
    (M : Submonoid R) [IsLocalization M S] (a : I)
    (P : Ideal (chartRing I a)) [P.IsPrime]
    (Q : Ideal (chartRing (I.map (algebraMap R S))
      (mappedElement I (algebraMap R S) a))) [Q.IsPrime]
    (hPQ : P = Q.comap (chartMap I (algebraMap R S) a)) :
    Function.Bijective (Localization.localRingHom P Q
      (chartMap I (algebraMap R S) a) hPQ) := by
  subst P
  exact localization_localRingHom_bijective I M a Q

variable (I : Ideal R) (a : I) (m : Ideal R) [m.IsPrime]
variable (P : Ideal (chartRing I a)) [P.IsPrime]
variable (hPm : P.comap (chartBaseMap I a) = m)

/-- The original chart stalk is identified with the stalk of the blowup chart
over the original centre localization, through the original chart map. -/
def originalChartStalkEquiv :
    Localization.AtPrime P ≃+* Localization.AtPrime (localizedChartPrime I a m P hPm) :=
  RingEquiv.ofBijective
    (Localization.localRingHom P (localizedChartPrime I a m P hPm)
      (chartMap I (algebraMap R (Localization.AtPrime m)) a)
      (localizedChartPrime_comap I a m P hPm).symm)
    (localization_localRingHom_bijective_of_comap I m.primeCompl a P
      (localizedChartPrime I a m P hPm) (localizedChartPrime_comap I a m P hPm).symm)

@[simp]
theorem originalChartStalkEquiv_to_map (z : chartRing I a) :
    originalChartStalkEquiv I a m P hPm (algebraMap _ (Localization.AtPrime P) z) =
      algebraMap _ (Localization.AtPrime (localizedChartPrime I a m P hPm))
        (chartMap I (algebraMap R (Localization.AtPrime m)) a z) :=
  Localization.localRingHom_to_map _ _ _ (localizedChartPrime_comap I a m P hPm).symm z

@[simp]
theorem originalChartStalkEquiv_baseMap (r : R) :
    originalChartStalkEquiv I a m P hPm
      (algebraMap _ (Localization.AtPrime P) (chartBaseMap I a r)) =
      algebraMap _ (Localization.AtPrime (localizedChartPrime I a m P hPm))
        (chartBaseMap (I.map (algebraMap R (Localization.AtPrime m)))
          (mappedElement I (algebraMap R (Localization.AtPrime m)) a)
          (algebraMap R (Localization.AtPrime m) r)) := by
  rw [originalChartStalkEquiv_to_map, chartMap_baseMap]
  rfl

@[simp]
theorem originalChartStalkEquiv_fraction (b : I) :
    originalChartStalkEquiv I a m P hPm
      (algebraMap _ (Localization.AtPrime P) (chartFraction I a b)) =
      algebraMap _ (Localization.AtPrime (localizedChartPrime I a m P hPm))
        (chartFraction (I.map (algebraMap R (Localization.AtPrime m)))
          (mappedElement I (algebraMap R (Localization.AtPrime m)) a)
          (mappedElement I (algebraMap R (Localization.AtPrime m)) b)) := by
  rw [originalChartStalkEquiv_to_map, chartMap_fraction]

end KltDP.Geometry.AffineBlowupChartBaseChange
