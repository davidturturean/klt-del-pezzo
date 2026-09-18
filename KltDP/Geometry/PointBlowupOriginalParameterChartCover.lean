import KltDP.Geometry.AffineBlowupParameterChartPoints
import KltDP.Geometry.AffineBlowupChartLocalizationPoint
import KltDP.Geometry.AffineBlowupChartBaseChangeEtale
import KltDP.Geometry.PointBlowupChartStalkAtCenter

/-!
# Coverage by the original numerators of a local parameter pair

The original Rees point is lifted by its already constructed localized
chart prime. Parameter-chart coverage is used on that same localized
Rees scheme. The proved original chart/global base-change square maps
the selected chart point back to the fixed original point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

namespace AffineBlowup

open AffineBlowupChartBaseChange

variable {R : Type u} [CommRing R] (I : Ideal R) (m : PrimeSpectrum R)

/-- Local generation at the actual image prime suffices for coverage by
the two original numerator charts at the original Rees point. -/
theorem exists_original_parameter_chart_over_prime (a b : I)
    (hspan : Ideal.span {algebraMap R (Localization.AtPrime m.asIdeal) (a : R),
      algebraMap R (Localization.AtPrime m.asIdeal) (b : R)} =
        I.map (algebraMap R (Localization.AtPrime m.asIdeal)))
    (y : scheme I) (hy : (toSpec I).base y = m) :
    ∃ d : I, (d = a ∨ d = b) ∧
      ∃ P : PrimeSpectrum (chartRing I d), (chartι I d).base P = y := by
  let ρ := algebraMap R (Localization.AtPrime m.asIdeal)
  let J := I.map ρ
  obtain ⟨t, p, hp⟩ := (degreeOneAffineCover I).openCover.exists_eq y
  change (chartι I t).base p = y at hp
  have hpmPoints : PrimeSpectrum.comap (chartBaseMap I t) p = m := by
    calc
      PrimeSpectrum.comap (chartBaseMap I t) p = (toSpec I).base ((chartι I t).base p) := by
        have hs := congrArg (fun f : Spec (CommRingCat.of (chartRing I t)) ⟶
          Spec (CommRingCat.of R) => f.base p) (chartι_toSpec I t)
        exact hs.symm
      _ = (toSpec I).base y := congrArg (toSpec I).base hp
      _ = m := hy
  have hpm : p.asIdeal.comap (chartBaseMap I t) = m.asIdeal :=
    congrArg PrimeSpectrum.asIdeal hpmPoints
  let Q : PrimeSpectrum (chartRing J (mappedElement I ρ t)) :=
    ⟨localizedChartPrime I t m.asIdeal p.asIdeal hpm, inferInstance⟩
  have hQ : PrimeSpectrum.comap (chartMap I ρ t) Q = p := by
    apply PrimeSpectrum.ext
    exact localizedChartPrime_comap I t m.asIdeal p.asIdeal hpm
  have hyQ : (openBaseChangeMap I ρ).base
      ((chartι J (mappedElement I ρ t)).base Q) = y := by
    calc
      _ = (chartι I t).base (PrimeSpectrum.comap (chartMap I ρ t) Q) :=
        (congrArg (fun f : Spec (CommRingCat.of (chartRing J (mappedElement I ρ t))) ⟶
          scheme I => f.base Q) (chartMap_chartι I ρ t)).symm
      _ = (chartι I t).base p := congrArg (chartι I t).base hQ
      _ = y := hp
  obtain ⟨d, hd, P, hP⟩ := exists_parameter_chart_point J
    (mappedElement I ρ a) (mappedElement I ρ b) hspan
    ((chartι J (mappedElement I ρ t)).base Q)
  rcases hd with hda | hdb
  · subst d
    refine ⟨a, Or.inl rfl, PrimeSpectrum.comap (chartMap I ρ a) P, ?_⟩
    calc
      _ = (openBaseChangeMap I ρ).base ((chartι J (mappedElement I ρ a)).base P) :=
        congrArg (fun f : Spec (CommRingCat.of (chartRing J (mappedElement I ρ a))) ⟶
          scheme I => f.base P) (chartMap_chartι I ρ a)
      _ = (openBaseChangeMap I ρ).base ((chartι J (mappedElement I ρ t)).base Q) :=
        congrArg (openBaseChangeMap I ρ).base hP
      _ = y := hyQ
  · subst d
    refine ⟨b, Or.inr rfl, PrimeSpectrum.comap (chartMap I ρ b) P, ?_⟩
    calc
      _ = (openBaseChangeMap I ρ).base ((chartι J (mappedElement I ρ b)).base P) :=
        congrArg (fun f : Spec (CommRingCat.of (chartRing J (mappedElement I ρ b))) ⟶
          scheme I => f.base P) (chartMap_chartι I ρ b)
      _ = (openBaseChangeMap I ρ).base ((chartι J (mappedElement I ρ t)).base Q) :=
        congrArg (openBaseChangeMap I ρ).base hP
      _ = y := hyQ

end AffineBlowup

namespace PointBlowupChartStalk

open AffineBlowup PointBlowupGluing

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))

/-- Every actual point over the original centre lies in an original
chart from any pair generating the original localized centre. -/
theorem exists_original_parameter_chart_at_center (a b : q.asIdeal)
    (hspan : Ideal.span {algebraMap R (Localization.AtPrime q.asIdeal) (a : R),
      algebraMap R (Localization.AtPrime q.asIdeal) (b : R)} =
        q.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)))
    (y : PointBlowupGluing.scheme j q hclosed)
    (hy : (projection j q hclosed).base y = j.base q) :
    ∃ d : q.asIdeal, (d = a ∨ d = b) ∧
      ∃ P : PrimeSpectrum (chartRing q.asIdeal d),
        (chartInclusion j q hclosed d).base P = y := by
  rcases pieces_cover j q hclosed y with ⟨z, hz⟩ | ⟨z, hz⟩
  · have hzq : (toSpec q.asIdeal).base z = q := by
      apply j.isOpenEmbedding.injective
      calc
        _ = (projection j q hclosed).base ((affineBlowupι j q hclosed).base z) :=
          (congrArg (fun f : AffineBlowup.scheme q.asIdeal ⟶ X => f.base z)
            (affineBlowupι_projection j q hclosed)).symm
        _ = (projection j q hclosed).base y := congrArg (projection j q hclosed).base hz
        _ = j.base q := hy
    obtain ⟨d, hd, P, hP⟩ := exists_original_parameter_chart_over_prime q.asIdeal q a b hspan z hzq
    exact ⟨d, hd, P, (congrArg (affineBlowupι j q hclosed).base hP).trans hz⟩
  · have hbase : (puncture j q hclosed).ι.base z = j.base q := by
      calc
        _ = (projection j q hclosed).base ((complementι j q hclosed).base z) :=
          (congrArg (fun f : (puncture j q hclosed).toScheme ⟶ X => f.base z)
            (complementι_projection j q hclosed)).symm
        _ = (projection j q hclosed).base y := congrArg (projection j q hclosed).base hz
        _ = j.base q := hy
    have hznot : (puncture j q hclosed).ι.base z ∉ ({j.base q} : Set X) := z.property
    exact False.elim (hznot (Set.mem_singleton_iff.mpr hbase))

end PointBlowupChartStalk
end KltDP.Geometry
