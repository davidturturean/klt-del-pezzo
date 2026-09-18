import KltDP.Geometry.AffineBlowupCover
import KltDP.Geometry.AffineBlowupConormal
import KltDP.Geometry.SurfaceRegularCharts

/-!
# Original points and stalks on the two parameter charts

The original ideal-generator affine cover produces a parameter-chart
point for every point of the same Rees scheme. Equality of the original
chart images preserves the actual centre condition by the original
projection square. The comparison of native local rings is composed
from their original open-immersion stalk maps and that point equality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineBlowup

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Every original Rees point lies in one of its two actual generating charts. -/
theorem exists_parameter_chart_point (a b : I)
    (hI : Ideal.span {(a : R), (b : R)} = I) (y : scheme I) :
    ∃ d : I, (d = a ∨ d = b) ∧
      ∃ p : PrimeSpectrum (chartRing I d), (chartι I d).base p = y := by
  let s : Fin 2 → I := ![a, b]
  have hspan : Ideal.span (Set.range (fun i => (s i : R))) = I := by
    have hfun : (fun i => (s i : R)) = ![(a : R), (b : R)] := by
      funext i
      fin_cases i <;> rfl
    rw [hfun, Matrix.range_cons_cons_empty]
    exact hI
  have hchoice : ∀ i : Fin 2, s i = a ∨ s i = b := by
    intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨i, p, hp⟩ := (generatingAffineCover I s hspan).openCover.exists_eq y
  change (chartι I (s i)).base p = y at hp
  exact ⟨s i, hchoice i, p, hp⟩

/-- Two original chart points with the same Rees image have the same
image in the original base spectrum. -/
theorem chartPoint_comap_eq (a b : I)
    (p : PrimeSpectrum (chartRing I a)) (q : PrimeSpectrum (chartRing I b))
    (h : (chartι I a).base p = (chartι I b).base q) :
    PrimeSpectrum.comap (chartBaseMap I a) p = PrimeSpectrum.comap (chartBaseMap I b) q := by
  have heq := congrArg (toSpec I).base h
  change (chartι I a ≫ toSpec I).base p = (chartι I b ≫ toSpec I).base q at heq
  simp only [chartι_toSpec] at heq
  exact heq

/-- The actual centre containment is preserved when selecting another
original chart through the same Rees point. -/
theorem chartPoint_center_of_eq (a b : I)
    (p : PrimeSpectrum (chartRing I a)) (q : PrimeSpectrum (chartRing I b))
    (h : (chartι I a).base p = (chartι I b).base q)
    (hp : chartCenterIdeal I a ≤ p.asIdeal) :
    chartCenterIdeal I b ≤ q.asIdeal := by
  have hbase := chartPoint_comap_eq I a b p q h
  have hpc : I ≤ p.asIdeal.comap (chartBaseMap I a) :=
    Ideal.map_le_iff_le_comap.mp hp
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr
  change r ∈ (PrimeSpectrum.comap (chartBaseMap I b) q).asIdeal
  rw [← hbase]
  exact hpc hr

/-- Native local rings on two actual charts are compared through the
original common scheme stalk, with only the proved chart-point equality. -/
def parameterChartStalkEquiv (a b : I)
    (p : PrimeSpectrum (chartRing I a)) (q : PrimeSpectrum (chartRing I b))
    (h : (chartι I a).base p = (chartι I b).base q) :
    Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal :=
  (openImmersionStalkLocalizationEquiv (chartι I a) p).symm.trans
    (((scheme I).presheaf.stalkCongr (.of_eq h)).commRingCatIsoToRingEquiv.trans
      (openImmersionStalkLocalizationEquiv (chartι I b) q))

end KltDP.Geometry.AffineBlowup
