import KltDP.Geometry.AffineBlowupChartLocalizationPoint
import KltDP.Geometry.AffineBlowupChartBaseChangeEtale
import KltDP.Geometry.AffineBlowupFiber

/-!
# The entire original point fiber from the blowup of the original local ring

The canonical map from the center fiber of the localized Rees blowup has
exactly the original point fiber as its image. Surjectivity uses the already
constructed original chart-prime lifts, with their original comap equality.
No source-fiber model or base-change-surjectivity assumption is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.LocalizedBlowupCenterFiber

open AffineBlowup AffineBlowupChartBaseChange

variable {R : Type u} [CommRing R]

/-- Membership in the image of the actual scheme-theoretic center fiber
is precisely containment of the original center ideal in the image prime. -/
theorem mem_range_centerFiberι_iff (I : Ideal R) (y : scheme I) :
    y ∈ Set.range (centerFiberι I).base ↔ I ≤ ((toSpec I).base y).asIdeal := by
  rw [centerFiberι, Scheme.Pullback.range_fst]
  change (toSpec I).base y ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) ↔ _
  rw [PrimeSpectrum.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  rfl

/-- The original localized center fiber maps canonically to the original
Rees blowup through the original center inclusion and base-change map. -/
def toOriginal (m : PrimeSpectrum R) :
    centerFiber (m.asIdeal.map (algebraMap R (Localization.AtPrime m.asIdeal))) ⟶
      scheme m.asIdeal :=
  centerFiberι _ ≫ openBaseChangeMap m.asIdeal (algebraMap R (Localization.AtPrime m.asIdeal))

/-- The image is the entire original point fiber, including every original
closed and generic fiber point. This holds for any original prime center. -/
theorem range_toOriginal (m : PrimeSpectrum R) :
    Set.range (toOriginal m).base = (toSpec m.asIdeal).base ⁻¹' {m} := by
  let ρ := algebraMap R (Localization.AtPrime m.asIdeal)
  let J := m.asIdeal.map ρ
  have hJ : J = IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal) :=
    Localization.AtPrime.map_eq_maximalIdeal
  apply Set.Subset.antisymm
  · rintro y ⟨z, rfl⟩
    let w : scheme J := (centerFiberι J).base z
    have hw : J ≤ ((toSpec J).base w).asIdeal :=
      (mem_range_centerFiberι_iff J w).mp ⟨z, rfl⟩
    have hp : ((toSpec J).base w).asIdeal =
        IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal) :=
      (Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal _)
        ((toSpec J).base w).isPrime.ne_top (hJ ▸ hw)).symm
    have hmap := congrArg (fun f : scheme J ⟶ Spec (CommRingCat.of R) => f.base w)
      (openBaseChangeMap_toSpec m.asIdeal ρ)
    change (toSpec m.asIdeal).base ((openBaseChangeMap m.asIdeal ρ).base w) =
      PrimeSpectrum.comap ρ ((toSpec J).base w) at hmap
    change (toSpec m.asIdeal).base ((openBaseChangeMap m.asIdeal ρ).base w) = m
    rw [hmap]
    apply PrimeSpectrum.ext
    change (((toSpec J).base w).asIdeal).comap ρ = m.asIdeal
    rw [hp]
    exact Localization.AtPrime.comap_maximalIdeal
  · intro y hy
    change (toSpec m.asIdeal).base y = m at hy
    obtain ⟨a, p, hp⟩ := (degreeOneAffineCover m.asIdeal).openCover.exists_eq y
    change (chartι m.asIdeal a).base p = y at hp
    have hpmPoints : PrimeSpectrum.comap (chartBaseMap m.asIdeal a) p = m := by
      calc
        _ = (toSpec m.asIdeal).base ((chartι m.asIdeal a).base p) :=
          (congrArg (fun f : Spec (CommRingCat.of (chartRing m.asIdeal a)) ⟶
            Spec (CommRingCat.of R) => f.base p) (chartι_toSpec m.asIdeal a)).symm
        _ = (toSpec m.asIdeal).base y := congrArg (toSpec m.asIdeal).base hp
        _ = m := hy
    have hpm : p.asIdeal.comap (chartBaseMap m.asIdeal a) = m.asIdeal :=
      congrArg PrimeSpectrum.asIdeal hpmPoints
    let Q : PrimeSpectrum (chartRing J (mappedElement m.asIdeal ρ a)) :=
      ⟨localizedChartPrime m.asIdeal a m.asIdeal p.asIdeal hpm, inferInstance⟩
    have hQ : Q.asIdeal.comap (chartMap m.asIdeal ρ a) = p.asIdeal :=
      localizedChartPrime_comap m.asIdeal a m.asIdeal p.asIdeal hpm
    have hbase : (chartBaseMap J (mappedElement m.asIdeal ρ a)).comp ρ =
        (chartMap m.asIdeal ρ a).comp (chartBaseMap m.asIdeal a) := by
      apply RingHom.ext
      intro r
      exact (chartMap_baseMap m.asIdeal ρ a r).symm
    have hJQ : J ≤ Q.asIdeal.comap (chartBaseMap J (mappedElement m.asIdeal ρ a)) := by
      apply Ideal.map_le_iff_le_comap.mpr
      rw [Ideal.comap_comap, hbase, ← Ideal.comap_comap, hQ, hpm]
    let w : scheme J := (chartι J (mappedElement m.asIdeal ρ a)).base Q
    have hw : w ∈ Set.range (centerFiberι J).base := by
      rw [mem_range_centerFiberι_iff]
      have hwbase := congrArg (fun f : Spec (CommRingCat.of
          (chartRing J (mappedElement m.asIdeal ρ a))) ⟶
          Spec (CommRingCat.of (Localization.AtPrime m.asIdeal)) => f.base Q)
        (chartι_toSpec J (mappedElement m.asIdeal ρ a))
      change (toSpec J).base ((chartι J (mappedElement m.asIdeal ρ a)).base Q) =
        PrimeSpectrum.comap (chartBaseMap J (mappedElement m.asIdeal ρ a)) Q at hwbase
      change J ≤ ((toSpec J).base ((chartι J (mappedElement m.asIdeal ρ a)).base Q)).asIdeal
      rw [hwbase]
      exact hJQ
    have hwmap : (openBaseChangeMap m.asIdeal ρ).base w = y := by
      calc
        _ = (chartι m.asIdeal a).base (PrimeSpectrum.comap (chartMap m.asIdeal ρ a) Q) :=
          (congrArg (fun f : Spec (CommRingCat.of
            (chartRing J (mappedElement m.asIdeal ρ a))) ⟶ scheme m.asIdeal => f.base Q)
            (chartMap_chartι m.asIdeal ρ a)).symm
        _ = (chartι m.asIdeal a).base p :=
          congrArg (chartι m.asIdeal a).base (PrimeSpectrum.ext hQ)
        _ = y := hp
    obtain ⟨z, hz⟩ := hw
    refine ⟨z, ?_⟩
    change (openBaseChangeMap m.asIdeal ρ).base ((centerFiberι J).base z) = y
    rw [hz]
    exact hwmap

end KltDP.Geometry.LocalizedBlowupCenterFiber

#print axioms KltDP.Geometry.LocalizedBlowupCenterFiber.range_toOriginal
