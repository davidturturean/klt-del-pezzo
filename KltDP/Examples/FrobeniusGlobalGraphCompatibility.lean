import KltDP.Examples.FrobeniusGlobalBlowupStages
import KltDP.Examples.FrobeniusGraphClosed

/-!
# The finite-stage local curves project to the actual closed projective graph

The ordinary polynomial projective-line chart is compared with the existing
homogeneous chart-power map. This identifies the monomial curve in the
actual product-plane chart with the restriction of the already constructed
global projective graph. Consequently the actual finite-stage residual
curve morphisms project through that closed graph.

All coordinate powers fix the original coefficients. No characteristic
assumption is needed for these comparisons. This is a comparison of actual
morphisms, not an assertion that a supplied local curve is already the
scheme-theoretic closure defining a global strict transform.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusGlobalGraphCompatibility

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
open FrobeniusProductPlaneChart FrobeniusGlobalBlowupStages

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- Ordinary polynomial coordinates raised to `p`, with all coefficients fixed. -/
def polynomialPowerHom (p : ℕ) : Polynomial k →+* Polynomial k :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.X ^ p)

@[simp] theorem polynomialPowerHom_C (p : ℕ) (r : k) :
    polynomialPowerHom p (Polynomial.C r) = Polynomial.C r := by
  simp [polynomialPowerHom]

@[simp] theorem polynomialPowerHom_X (p : ℕ) :
    polynomialPowerHom (k := k) p Polynomial.X = Polynomial.X ^ p := by
  simp [polynomialPowerHom]

/-- Renaming the single affine coordinate intertwines the actual two
coefficient-fixed power homomorphisms. -/
theorem oneVariablePolynomialEquiv_affinePower (p : ℕ) :
    (ProjectiveLineComparison.oneVariablePolynomialEquiv k).toRingHom.comp (affinePowerHom p) =
      (polynomialPowerHom p).comp
        (ProjectiveLineComparison.oneVariablePolynomialEquiv k).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change ProjectiveLineComparison.oneVariablePolynomialEquiv k
        (affinePowerHom p (MvPolynomial.C r)) =
      polynomialPowerHom p (ProjectiveLineComparison.oneVariablePolynomialEquiv k (MvPolynomial.C r))
    have hC : ProjectiveLineComparison.oneVariablePolynomialEquiv k (MvPolynomial.C r) =
        Polynomial.C r := (ProjectiveLineComparison.oneVariablePolynomialEquiv k).commutes r
    rw [affinePowerHom_C, hC, polynomialPowerHom_C]
  · intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change ProjectiveLineComparison.oneVariablePolynomialEquiv k
        (affinePowerHom p (MvPolynomial.X (0 : Fin 1))) =
      polynomialPowerHom p
        (ProjectiveLineComparison.oneVariablePolynomialEquiv k (MvPolynomial.X (0 : Fin 1)))
    rw [affinePowerHom_X, map_pow,
      ProjectiveLineComparison.oneVariablePolynomialEquiv_X, polynomialPowerHom_X]

/-- The actual homogeneous-chart power map becomes the ordinary polynomial
substitution under the proved chart ring equivalence. -/
theorem firstChartPolynomialEquiv_chartPower (p : ℕ) :
    (ProjectiveLineComparison.firstChartPolynomialEquiv k).toRingHom.comp
        (chartPowerMap p (ProjectiveChart.coordinate k 1) (homogeneousPowerHom_X p 0)) =
      (polynomialPowerHom p).comp
        (ProjectiveLineComparison.firstChartPolynomialEquiv k).toRingHom := by
  apply RingHom.ext
  intro z
  change ProjectiveLineComparison.oneVariablePolynomialEquiv k
      (ProjectiveChart.dehomogenize k 1
        (chartPowerMap p (ProjectiveChart.coordinate k 1) (homogeneousPowerHom_X p 0) z)) =
    polynomialPowerHom p (ProjectiveLineComparison.oneVariablePolynomialEquiv k
      (ProjectiveChart.dehomogenize k 1 z))
  have hz := RingHom.congr_fun (dehomogenize_comp_chartPowerMap (k := k) p) z
  change ProjectiveChart.dehomogenize k 1
      (chartPowerMap p (ProjectiveChart.coordinate k 1) (homogeneousPowerHom_X p 0) z) =
    affinePowerHom p (ProjectiveChart.dehomogenize k 1 z) at hz
  rw [hz]
  exact RingHom.congr_fun (oneVariablePolynomialEquiv_affinePower p)
    (ProjectiveChart.dehomogenize k 1 z)

/-- The actual projective power morphism has its expected formula on the
ordinary polynomial affine-line chart. -/
@[reassoc] theorem polynomialChartMap_power (p : ℕ) :
    ProjectiveLineComparison.polynomialChartMap k 0 ≫ projectivePowerMorphism p =
      Spec.map (CommRingCat.ofHom (polynomialPowerHom (k := k) p)) ≫
        ProjectiveLineComparison.polynomialChartMap k 0 := by
  have hc : ProjectiveChart.chartMorphism k 1 ≫ projectivePowerMorphism p =
      Spec.map (CommRingCat.ofHom
        (chartPowerMap p (ProjectiveChart.coordinate k 1) (homogeneousPowerHom_X p 0))) ≫
          ProjectiveChart.chartMorphism k 1 := chart_projectivePowerMorphism p 0
  change (Spec.map (CommRingCat.ofHom
      (ProjectiveLineComparison.firstChartPolynomialEquiv k).toRingHom) ≫
        ProjectiveChart.chartMorphism k 1) ≫ projectivePowerMorphism p =
    Spec.map (CommRingCat.ofHom (polynomialPowerHom p)) ≫
      (Spec.map (CommRingCat.ofHom
        (ProjectiveLineComparison.firstChartPolynomialEquiv k).toRingHom) ≫ ProjectiveChart.chartMorphism k 1)
  rw [Category.assoc, hc, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, firstChartPolynomialEquiv_chartPower]

/-- The first actual coordinate of the monomial curve is its parameter. -/
theorem curveInPlane_firstCoordinate (p : ℕ) :
    curveInPlane (k := k) p ≫ Spec.map (CommRingCat.ofHom firstCoordinateMap) =
      𝟙 (Spec (CommRingCat.of (Polynomial k))) := by
  have h : (Polynomial.evalRingHom (Polynomial.X ^ p : Polynomial k)).comp
      firstCoordinateMap = RingHom.id (Polynomial k) := by
    apply RingHom.ext
    intro f
    simp [firstCoordinateMap]
  rw [curveInPlane, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    h, CommRingCat.ofHom_id, Spec.map_id]

/-- The second actual coordinate is the parameter's `p`th power. -/
theorem curveInPlane_secondCoordinate (p : ℕ) :
    curveInPlane (k := k) p ≫ Spec.map (CommRingCat.ofHom secondCoordinateMap) =
      Spec.map (CommRingCat.ofHom (polynomialPowerHom (k := k) p)) := by
  have h : (Polynomial.evalRingHom (Polynomial.X ^ p : Polynomial k)).comp
      secondCoordinateMap = polynomialPowerHom p := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [secondCoordinateMap, polynomialPowerHom]
    · simp [secondCoordinateMap, polynomialPowerHom]
  rw [curveInPlane, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- The monomial curve in the actual product-plane chart is exactly the
restriction of the already constructed global projective graph morphism. -/
theorem curveInPlane_productChart (p : ℕ) :
    curveInPlane (k := k) p ≫ planeChart =
      ProjectiveLineComparison.polynomialChartMap k 0 ≫ projectiveGraphMorphism p := by
  apply pullback.hom_ext
  · rw [Category.assoc, planeChart_fst, ← Category.assoc,
      curveInPlane_firstCoordinate, Category.id_comp]
    simp only [Category.assoc, projectiveGraphMorphism, pullback.lift_fst, Category.comp_id]
  · rw [Category.assoc, planeChart_snd, ← Category.assoc,
      curveInPlane_secondCoordinate, ← polynomialChartMap_power]
    simp only [Category.assoc, projectiveGraphMorphism, pullback.lift_snd]

/-- The actual stage residual curve projects to the original global graph
through its ordinary polynomial projective-line chart. -/
theorem residualCurve_toProjectiveGraph (n m : ℕ) :
    (projectiveProductInitial (k := k)).residualCurve n m ≫ projectiveContactProjection n =
      ProjectiveLineComparison.polynomialChartMap k 0 ≫ projectiveGraphMorphism (m + n) := by
  change (projectiveProductInitial (k := k)).residualCurve n m ≫
      (projectiveProductInitial (k := k)).toInitial n = _
  rw [PlaneChartedScheme.residualCurve_toInitial]
  exact curveInPlane_productChart (m + n)

/-- This composite factors through the actual closed graph scheme, with
its already proved equalizer inclusion. No global strict-transform closure
is supplied or inferred from this factorization. -/
theorem residualCurve_factors_closedGraph (n m : ℕ) :
    (projectiveProductInitial (k := k)).residualCurve n m ≫ projectiveContactProjection n =
      (ProjectiveLineComparison.polynomialChartMap k 0 ≫ lineToGraph (m + n)) ≫
        graphι (m + n) := by
  rw [residualCurve_toProjectiveGraph, Category.assoc, lineToGraph_ι]

end KltDP.Examples.FrobeniusGlobalGraphCompatibility
