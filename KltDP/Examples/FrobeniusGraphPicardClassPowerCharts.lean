import KltDP.Examples.FrobeniusGraphPicardClassCharts
import KltDP.Examples.FrobeniusGlobalGraphCompatibility

/-!
# The original power morphism in both reciprocal polynomial charts

The homogeneous localization map sends each actual coordinate fraction to
its p-th power. Transport by the existing polynomial chart equivalences
gives the same coefficient-fixed polynomial power map on both charts.
Consequently the existing monomial curve gives the original graph in both
diagonal product charts, including the chart at infinity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassPowerCharts

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectiveMorphism FrobeniusGlobalGraphCompatibility
open FrobeniusProductPlaneChart FrobeniusGraphPicardClassCharts
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGraphClosed

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- The original map acts on every original homogeneous coordinate fraction. -/
theorem chartPowerMap_coordinate (p : ℕ) (i j : Fin 2) :
    chartPowerMap p (MvPolynomial.X i) (homogeneousPowerHom_X p i)
      (coordinate k i j) = coordinate k i j ^ p := by
  apply HomogeneousLocalization.val_injective
  rw [chartPowerMap, powerLocalizationMap_val, HomogeneousLocalization.val_pow]
  simp only [coordinate, HomogeneousLocalization.Away.val_mk, pow_one,
    Localization.mk_eq_mk', IsLocalization.map_mk', homogeneousPowerHom_X,
    ← IsLocalization.mk'_pow]
  apply congrArg (IsLocalization.mk'
    (Localization.Away (MvPolynomial.X i : ProjectiveChart.homogeneousRing k 1))
    ((MvPolynomial.X j : ProjectiveChart.homogeneousRing k 1) ^ p))
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow]

/-- The other homogeneous index supplies the polynomial chart coordinate. -/
def otherIndex (i : Fin 2) : Fin 2 := Equiv.swap 0 1 i

theorem chartPolynomialEquiv_otherCoordinate (i : Fin 2) :
    ProjectiveLineComparison.chartPolynomialEquiv k i (coordinate k i (otherIndex i)) = Polynomial.X := by
  fin_cases i
  · simpa only [otherIndex, Equiv.swap_apply_left, ProjectiveLineComparison.chartPolynomialEquiv,
      Fin.cases_zero] using firstChartPolynomialEquiv_coordinate k
  · simpa only [otherIndex, Equiv.swap_apply_right, ProjectiveLineComparison.chartPolynomialEquiv,
      Fin.cases_succ, Fin.cases_zero] using secondChartPolynomialEquiv_coordinate k

/-- The ring map in either original chart is the same polynomial substitution. -/
theorem chartPolynomialEquiv_power (p : ℕ) (i : Fin 2) :
    (ProjectiveLineComparison.chartPolynomialEquiv k i).toRingHom.comp
        (chartPowerMap p (MvPolynomial.X i) (homogeneousPowerHom_X p i)) =
      (polynomialPowerHom p).comp (ProjectiveLineComparison.chartPolynomialEquiv k i).toRingHom := by
  let e := ProjectiveLineComparison.chartPolynomialEquiv k i
  let f : chartRing k i →+* chartRing k i :=
    chartPowerMap (k := k) p (MvPolynomial.X i) (homogeneousPowerHom_X p i)
  have hc (r : k) : e.symm (Polynomial.C r) = ProjectiveLineComparison.chartConstants k i r := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (chartPolynomialEquiv_constants k i r).symm
  have hx : e.symm Polynomial.X = coordinate k i (otherIndex i) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (chartPolynomialEquiv_otherCoordinate i).symm
  have hf : (e.toRingHom.comp f).comp e.symm.toRingHom = polynomialPowerHom p := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [hc]
      change e (chartPowerMap p (MvPolynomial.X i) (homogeneousPowerHom_X p i)
        (FrobeniusProjectiveMorphism.chartConstants (MvPolynomial.X i) r)) = _
      rw [chartPowerMap_constants]
      exact (chartPolynomialEquiv_constants k i r).trans (polynomialPowerHom_C p r).symm
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [hx]
      change e (chartPowerMap p (MvPolynomial.X i) (homogeneousPowerHom_X p i)
        (coordinate k i (otherIndex i))) = polynomialPowerHom p Polynomial.X
      rw [chartPowerMap_coordinate, map_pow, chartPolynomialEquiv_otherCoordinate,
        polynomialPowerHom_X]
  apply RingHom.ext
  intro z
  have hz := RingHom.congr_fun hf (e z)
  change e (f (e.symm (e z))) = polynomialPowerHom p (e z) at hz
  rw [e.symm_apply_apply] at hz
  exact hz

/-- Both original polynomial charts intertwine the original global power map. -/
@[reassoc]
theorem polynomialChartMap_power_both (p : ℕ) (i : Fin 2) :
    polynomialChartMap k i ≫ projectivePowerMorphism p =
      Spec.map (CommRingCat.ofHom (polynomialPowerHom (k := k) p)) ≫
        polynomialChartMap k i := by
  have hc : chartImmersion k i ≫ projectivePowerMorphism p =
      Spec.map (CommRingCat.ofHom
        (chartPowerMap p (MvPolynomial.X i) (homogeneousPowerHom_X p i))) ≫
          chartImmersion k i := chart_projectivePowerMorphism p i
  change (Spec.map (CommRingCat.ofHom (ProjectiveLineComparison.chartPolynomialEquiv k i).toRingHom) ≫
      chartImmersion k i) ≫ projectivePowerMorphism p =
    Spec.map (CommRingCat.ofHom (polynomialPowerHom p)) ≫
      (Spec.map (CommRingCat.ofHom (ProjectiveLineComparison.chartPolynomialEquiv k i).toRingHom) ≫ chartImmersion k i)
  rw [Category.assoc, hc, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, chartPolynomialEquiv_power]

/-- The original affine monomial graph gives the global graph also at infinity. -/
theorem curveInPlane_diagonalChart (p : ℕ) (i : Fin 2) :
    curveInPlane (k := k) p ≫ productChart i i =
      polynomialChartMap k i ≫ projectiveGraphMorphism p := by
  apply pullback.hom_ext
  · rw [Category.assoc, productChart_fst, ← Category.assoc,
      curveInPlane_firstCoordinate, Category.id_comp]
    simp only [Category.assoc, projectiveGraphMorphism, pullback.lift_fst, Category.comp_id]
  · rw [Category.assoc, productChart_snd, ← Category.assoc,
      curveInPlane_secondCoordinate, ← polynomialChartMap_power_both]
    simp only [Category.assoc, projectiveGraphMorphism, pullback.lift_snd]

end KltDP.Examples.FrobeniusGraphPicardClassPowerCharts
