import KltDP.Geometry.AffineBlowupChartLocalizationStalks

/-! Lifting an original Rees-chart prime after localizing its base at its image. -/

noncomputable section

namespace KltDP.Geometry.AffineBlowupChartBaseChange

open AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
variable (m : Ideal R) [m.IsPrime]
variable (P : Ideal (chartRing I a)) [P.IsPrime]

/-- The original base map into the original chart stalk. -/
def chartStalkBaseMap : R →+* Localization.AtPrime P :=
  (algebraMap (chartRing I a) (Localization.AtPrime P)).comp (chartBaseMap I a)

theorem chartStalkBaseMap_regular :
    chartStalkBaseMap I a P (a : R) ∈ nonZeroDivisors (Localization.AtPrime P) :=
  IsLocalization.nonZeroDivisors_le_comap P.primeCompl (Localization.AtPrime P)
    (chartBaseMap_equation_mem_nonZeroDivisors I a)

theorem chartStalkBaseMap_center :
    I.map (chartStalkBaseMap I a P) =
      Ideal.span {chartStalkBaseMap I a P (a : R)} := by
  rw [chartStalkBaseMap, ← Ideal.map_map, map_chartBaseMap_ideal, Ideal.map_span]
  simp only [Set.image_singleton, RingHom.comp_apply]

variable (hPm : P.comap (chartBaseMap I a) = m)

/-- The base localization acts on the actual chart stalk because every element
outside the original centre becomes a unit there. -/
def localizedBaseToChartStalk (hPm : P.comap (chartBaseMap I a) = m) :
    Localization.AtPrime m →+* Localization.AtPrime P :=
  IsLocalization.lift (S := Localization.AtPrime m)
    (g := chartStalkBaseMap I a P) fun r : m.primeCompl => by
      have hrP : chartBaseMap I a (r : R) ∉ P := by
        intro hr
        apply r.property
        exact Eq.mp (congrArg (fun J : Ideal R => (r : R) ∈ J) hPm)
          (show (r : R) ∈ P.comap (chartBaseMap I a) from hr)
      exact IsLocalization.map_units (M := P.primeCompl) (Localization.AtPrime P)
        ⟨chartBaseMap I a (r : R), hrP⟩

@[simp]
theorem localizedBaseToChartStalk_to_map (r : R) :
    localizedBaseToChartStalk I a m P hPm (algebraMap R (Localization.AtPrime m) r) =
      chartStalkBaseMap I a P r :=
  IsLocalization.lift_eq _ r

theorem localizedBaseToChartStalk_regular :
    localizedBaseToChartStalk I a m P hPm
        (mappedElement I (algebraMap R (Localization.AtPrime m)) a : Localization.AtPrime m)
      ∈ nonZeroDivisors (Localization.AtPrime P) := by
  change localizedBaseToChartStalk I a m P hPm
      (algebraMap R (Localization.AtPrime m) (a : R)) ∈ _
  rw [localizedBaseToChartStalk_to_map]
  exact chartStalkBaseMap_regular I a P

theorem localizedBaseToChartStalk_center :
    (I.map (algebraMap R (Localization.AtPrime m))).map
        (localizedBaseToChartStalk I a m P hPm) =
      Ideal.span {localizedBaseToChartStalk I a m P hPm
        (mappedElement I (algebraMap R (Localization.AtPrime m)) a : Localization.AtPrime m)} := by
  rw [Ideal.map_map]
  have heq : (localizedBaseToChartStalk I a m P hPm).comp
      (algebraMap R (Localization.AtPrime m)) = chartStalkBaseMap I a P := by
    ext r
    exact localizedBaseToChartStalk_to_map I a m P hPm r
  rw [heq]
  change I.map (chartStalkBaseMap I a P) = Ideal.span
    {localizedBaseToChartStalk I a m P hPm (algebraMap R (Localization.AtPrime m) (a : R))}
  rw [localizedBaseToChartStalk_to_map, chartStalkBaseMap_center]

/-- The localized chart maps into the original chart stalk by the already
proved Rees-chart universal property. -/
def localizedChartToStalk (hPm : P.comap (chartBaseMap I a) = m) :
    chartRing (I.map (algebraMap R (Localization.AtPrime m)))
      (mappedElement I (algebraMap R (Localization.AtPrime m)) a) →+*
        Localization.AtPrime P :=
  chartLift _ _ (localizedBaseToChartStalk I a m P hPm)
    (localizedBaseToChartStalk_regular I a m P hPm)
    (localizedBaseToChartStalk_center I a m P hPm).le

/-- The lift retains the original ring map into the original stalk. -/
theorem localizedChartToStalk_comp_chartMap :
    (localizedChartToStalk I a m P hPm).comp
      (chartMap I (algebraMap R (Localization.AtPrime m)) a) =
        algebraMap (chartRing I a) (Localization.AtPrime P) := by
  have hcomp : ((localizedChartToStalk I a m P hPm).comp
      (chartMap I (algebraMap R (Localization.AtPrime m)) a)).comp (chartBaseMap I a) =
        chartStalkBaseMap I a P := by
    ext r
    simp only [RingHom.comp_apply, chartMap_baseMap, baseMap,
      localizedChartToStalk, chartLift_baseMap, localizedBaseToChartStalk_to_map]
  exact (chartLift_unique I a (chartStalkBaseMap I a P)
    (chartStalkBaseMap_regular I a P) (chartStalkBaseMap_center I a P).le _ hcomp).trans
      (chartLift_unique I a (chartStalkBaseMap I a P)
        (chartStalkBaseMap_regular I a P) (chartStalkBaseMap_center I a P).le
        (algebraMap (chartRing I a) (Localization.AtPrime P)) rfl).symm

/-- The corresponding prime is the inverse image of the maximal ideal of the
original chart stalk, rather than a supplied point-lifting witness. -/
def localizedChartPrime (hPm : P.comap (chartBaseMap I a) = m) : Ideal
    (chartRing (I.map (algebraMap R (Localization.AtPrime m)))
      (mappedElement I (algebraMap R (Localization.AtPrime m)) a)) :=
  (IsLocalRing.maximalIdeal (Localization.AtPrime P)).comap
    (localizedChartToStalk I a m P hPm)

instance localizedChartPrime_isPrime : (localizedChartPrime I a m P hPm).IsPrime := by
  dsimp only [localizedChartPrime]
  infer_instance

/-- Its image under the original localized chart map is exactly the original prime. -/
theorem localizedChartPrime_comap :
    (localizedChartPrime I a m P hPm).comap
      (chartMap I (algebraMap R (Localization.AtPrime m)) a) = P := by
  rw [localizedChartPrime, Ideal.comap_comap, localizedChartToStalk_comp_chartMap]
  exact Localization.AtPrime.comap_maximalIdeal

end KltDP.Geometry.AffineBlowupChartBaseChange
