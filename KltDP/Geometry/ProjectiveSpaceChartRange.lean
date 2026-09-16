import KltDP.Geometry.ProjectiveSpaceCoordinateCharts
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Points of one coordinate chart of `projectiveSpace k n` lying in another chart

For a point `q` of the chart `Spec (A_{(z_m)})` of `projectiveSpace k n`, its image in `P^n` lies in
the chart `D(z_i)` if and only if the fraction `z_i / z_m` (`chartFraction k n m i`, the pinned
`Away.isLocalizationElem`) is invertible at `q` (`coordinateChartMorphism_mem_range_iff`): the
overlap `D(z_m) ∩ D(z_i)` is the spectrum of `A_{(z_m z_i)} = A_{(z_m)}[1/(z_i/z_m)]` (pinned
`Away.isLocalization_mul`, `Proj.pullbackAwayιIso`, `PrimeSpectrum.localization_away_comap_range`,
`Scheme.Pullback.range_fst`).

Generic point-set facts used: the range of `Spec.map` of a localisation map away from `r` is the
basic open `D(r)` (`range_specMap_of_isLocalization_away`), the preimage of a basic open under
`Spec.map φ` is the basic open of the image (`specMap_base_mem_basicOpen_iff`), and an isomorphism
in front of a morphism does not change its range (`range_comp_base_of_isIso`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ProjectiveChart

section Generic

variable {X Y Z : Scheme.{u}}

/-- An isomorphism in front of a morphism does not change the range of the underlying map. -/
theorem range_comp_base_of_isIso (e : X ⟶ Y) [IsIso e] (f : Y ⟶ Z) :
    Set.range (e ≫ f).base = Set.range f.base := by
  have hsurj : Function.Surjective e.base := e.homeomorph.surjective
  rw [Scheme.comp_base, TopCat.coe_comp]
  exact hsurj.range_comp _

/-- The image of a point under `Spec.map φ` lies in `D(r)` iff the point lies in `D(φ r)`. -/
theorem specMap_base_mem_basicOpen_iff {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (y : Spec (CommRingCat.of S)) (r : R) :
    (Spec.map (CommRingCat.ofHom φ)).base y ∈ PrimeSpectrum.basicOpen r ↔
      y ∈ PrimeSpectrum.basicOpen (φ r) := by
  rw [Spec.map_base_apply]
  exact Iff.rfl

/-- The range of `Spec.map` of a localisation map away from `r` is the basic open `D(r)`. -/
theorem range_specMap_of_isLocalization_away {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (r : R) (h : letI := φ.toAlgebra; IsLocalization.Away r S) :
    Set.range (Spec.map (CommRingCat.ofHom φ)).base =
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
  letI := φ.toAlgebra
  haveI : IsLocalization.Away r S := h
  have hr := PrimeSpectrum.localization_away_comap_range S r
  rw [RingHom.algebraMap_toAlgebra] at hr
  have e : Set.range (Spec.map (CommRingCat.ofHom φ)).base =
      Set.range (PrimeSpectrum.comap φ) := rfl
  exact e.trans hr

end Generic

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

/-- The fraction `z_i / z_m` in the chart ring of `z_m` (the pinned localisation element of
`A_{(z_m z_i)} = A_{(z_m)}[1/(z_i/z_m)]`). -/
abbrev chartFraction (m i : Fin (n + 1)) : coordinateChartRing k n m :=
  HomogeneousLocalization.Away.isLocalizationElem (coordinate_mem k n m) (coordinate_mem k n i)

theorem chartFraction_eq (m i : Fin (n + 1)) :
    chartFraction k n m i =
      HomogeneousLocalization.Away.mk (grading k n) (coordinate_mem k n m) 1 (MvPolynomial.X i)
        (by simpa only [one_smul] using coordinate_mem k n i) := by
  unfold chartFraction HomogeneousLocalization.Away.isLocalizationElem
  congr 1
  exact pow_one _

/-- `A_{(z_m z_i)}` is the localisation of `A_{(z_m)}` away from `z_i/z_m`. -/
theorem toOverlapLeft_isLocalization (m i : Fin (n + 1)) :
    letI := (toOverlapLeft k n m i).toAlgebra
    IsLocalization.Away (chartFraction k n m i) (coordinateOverlapRing k n m i) :=
  HomogeneousLocalization.Away.isLocalization_mul (coordinate_mem k n m) (coordinate_mem k n i)
    rfl Nat.one_ne_zero

/-- The range of the restriction `Spec (A_{(z_m z_i)}) ⟶ Spec (A_{(z_m)})` is `D(z_i/z_m)`. -/
theorem range_specMap_toOverlapLeft (m i : Fin (n + 1)) :
    Set.range (Spec.map (CommRingCat.ofHom (toOverlapLeft k n m i))).base =
      (PrimeSpectrum.basicOpen (chartFraction k n m i) :
        Set (PrimeSpectrum (coordinateChartRing k n m))) :=
  range_specMap_of_isLocalization_away _ _ (toOverlapLeft_isLocalization k n m i)

/-- The range of the first projection of the overlap `D(z_m) ∩ D(z_i)` in the chart `D(z_m)`. -/
theorem range_pullback_fst_coordinateCharts (m i : Fin (n + 1)) :
    Set.range (pullback.fst (coordinateChartMorphism k n m) (coordinateChartMorphism k n i)).base =
      (PrimeSpectrum.basicOpen (chartFraction k n m i) :
        Set (PrimeSpectrum (coordinateChartRing k n m))) := by
  rw [← range_specMap_toOverlapLeft, ← coordinateOverlapIso_inv_fst, range_comp_base_of_isIso]

/-- **A point of the chart `D(z_m)` lies in the chart `D(z_i)` iff `z_i/z_m` is invertible
at it.** -/
theorem coordinateChartMorphism_mem_range_iff (m i : Fin (n + 1))
    (q : Spec (CommRingCat.of (coordinateChartRing k n m))) :
    (coordinateChartMorphism k n m).base q ∈ Set.range (coordinateChartMorphism k n i).base ↔
      q ∈ PrimeSpectrum.basicOpen (chartFraction k n m i) := by
  have h := Scheme.Pullback.range_fst (coordinateChartMorphism k n m)
    (coordinateChartMorphism k n i)
  rw [range_pullback_fst_coordinateCharts] at h
  exact (Set.ext_iff.mp h q).symm

end KltDP.Geometry.ProjectiveChart
