import KltDP.Examples.FrobeniusGlobalGraphCompatibility
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.CharP.Lemmas

/-!
# Actual translated Frobenius contact charts

The existing polynomial translation equivalence and its coefficientwise
extension give an actual automorphism of the polynomial plane. Composing
with the proved product-plane open chart moves the origin to `(a,a^p)`.
In characteristic `p`, the binomial identity proves that this chart takes
the local curve `v=u^p` to the actual original Frobenius graph.

Reuse: pinned `Polynomial.algEquivAevalXAddC`, `Polynomial.mapAlgEquiv`,
`AlgEquiv.restrictScalars`, and `add_pow_char`; the current official
Mathlib documentation retains these exact translation definitions. No
new polynomial equivalence proof or general smooth-coordinate theorem
is substituted. The file does not combine different blowup branches.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusTranslatedCharts

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusProductPlaneChart FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusGlobalGraphCompatibility

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- The pinned actual polynomial translation `t ↦ t+a`. -/
abbrev parameterTranslation (a : k) : Polynomial k ≃ₐ[k] Polynomial k :=
  Polynomial.algEquivAevalXAddC a

/-- Translation of both actual polynomial-plane coordinates, fixing `k`. -/
def coordinateTranslation (a b : k) : planeRing k ≃ₐ[k] planeRing k :=
  (Polynomial.mapAlgEquiv (parameterTranslation a)).trans
    ((Polynomial.algEquivAevalXAddC (Polynomial.C b)).restrictScalars k)

@[simp] theorem coordinateTranslation_C (a b : k) (f : Polynomial k) :
    coordinateTranslation a b (Polynomial.C f) = Polynomial.C (parameterTranslation a f) := by
  simp [coordinateTranslation]

@[simp] theorem coordinateTranslation_u (a b : k) :
    coordinateTranslation a b (uCoord (k := k)) = uCoord + planeConstants a := by
  rw [uCoord, coordinateTranslation_C]
  simp [parameterTranslation, planeConstants, uCoord]

@[simp] theorem coordinateTranslation_v (a b : k) :
    coordinateTranslation a b (vCoord (k := k)) = vCoord + planeConstants b := by
  simp [coordinateTranslation, vCoord, planeConstants]

@[simp] theorem coordinateTranslation_constants (a b r : k) :
    coordinateTranslation a b (planeConstants r) = planeConstants r :=
  (coordinateTranslation a b).commutes r

/-- The actual contravariant scheme translation, whose pullback is `u+a,v+b`. -/
def planeTranslationIso (a b : k) : plane k ≅ plane k :=
  Scheme.Spec.mapIso (coordinateTranslation a b).toRingEquiv.toCommRingCatIso.op

/-- The actual parameter-line translation with pullback `t+a`. -/
def parameterTranslationIso (a : k) :
    Spec (CommRingCat.of (Polynomial k)) ≅ Spec (CommRingCat.of (Polynomial k)) :=
  Scheme.Spec.mapIso (parameterTranslation a).toRingEquiv.toCommRingCatIso.op

@[reassoc] theorem planeTranslationIso_hom_structure (a b : k) :
    (planeTranslationIso a b).hom ≫ planeStructure = planeStructure := by
  have h : (coordinateTranslation a b).toRingHom.comp planeConstants = planeConstants := by
    apply RingHom.ext
    intro r
    exact coordinateTranslation_constants a b r
  change Spec.map (CommRingCat.ofHom (coordinateTranslation a b).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (planeConstants (k := k))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  rfl

/-- Evaluation at an actual pair of affine-plane coordinates. -/
def planeEvaluation (a b : k) : planeRing k →+* k :=
  (Polynomial.evalRingHom a).comp (Polynomial.evalRingHom (Polynomial.C b))

/-- Translating the actual origin yields the actual coordinate evaluation map. -/
theorem originEvaluation_translation (a b : k) :
    (originEvaluation (k := k)).comp (coordinateTranslation a b).toRingHom =
      planeEvaluation a b := by
  apply Polynomial.ringHom_ext
  · intro f
    change originEvaluation (coordinateTranslation a b (Polynomial.C f)) =
      planeEvaluation a b (Polynomial.C f)
    rw [coordinateTranslation_C]
    simp only [originEvaluation, planeEvaluation, RingHom.comp_apply,
      Polynomial.coe_evalRingHom, Polynomial.eval_C]
    rw [parameterTranslation, Polynomial.algEquivAevalXAddC_apply,
      ← Polynomial.comp_eq_aeval, Polynomial.eval_comp]
    simp
  · change originEvaluation (coordinateTranslation a b (vCoord (k := k))) =
      planeEvaluation a b vCoord
    rw [coordinateTranslation_v, map_add]
    simp [originEvaluation, planeEvaluation, vCoord, planeConstants]

/-- The original homogeneous point morphism agrees with ordinary polynomial evaluation. -/
theorem polynomialChartMap_evaluation (a : k) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫
      ProjectiveLineComparison.polynomialChartMap k 0 = pointMorphism a := by
  have h : (Polynomial.evalRingHom a).comp
      (ProjectiveLineComparison.oneVariablePolynomialEquiv k).toRingHom =
        parameterEvaluation a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have hC : ProjectiveLineComparison.oneVariablePolynomialEquiv k (MvPolynomial.C r) =
          Polynomial.C r := (ProjectiveLineComparison.oneVariablePolynomialEquiv k).commutes r
      simp [parameterEvaluation]
      rw [hC, Polynomial.eval_C]
    · intro i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simp [parameterEvaluation]
  have hc : (Polynomial.evalRingHom a).comp
      (ProjectiveLineComparison.firstChartPolynomialEquiv k).toRingHom =
        coordinateEvaluation a := by
    apply RingHom.ext
    intro z
    exact RingHom.congr_fun h (ProjectiveChart.dehomogenize k 1 z)
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫
    (Spec.map (CommRingCat.ofHom (ProjectiveLineComparison.firstChartPolynomialEquiv k).toRingHom) ≫
      ProjectiveChart.chartMorphism k 1) = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  rfl

/-- The actual origin in a translated plane chart is the previously constructed graph point. -/
theorem origin_translated_productChart (p : ℕ) (a : k) :
    originMorphism ≫ (planeTranslationIso a (a ^ p)).hom ≫ planeChart =
      graphPointMorphism p a := by
  have hOrigin : originMorphism ≫ (planeTranslationIso a (a ^ p)).hom =
      Spec.map (CommRingCat.ofHom (planeEvaluation a (a ^ p))) := by
    change Spec.map (CommRingCat.ofHom (originEvaluation (k := k))) ≫
      Spec.map (CommRingCat.ofHom (coordinateTranslation a (a ^ p)).toRingHom) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, originEvaluation_translation]
  have hFirst : (planeEvaluation a (a ^ p)).comp firstCoordinateMap =
      Polynomial.evalRingHom a := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [planeEvaluation, firstCoordinateMap]
    · simp [planeEvaluation, firstCoordinateMap]
  have hSecond : (planeEvaluation a (a ^ p)).comp secondCoordinateMap =
      Polynomial.evalRingHom (a ^ p) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [planeEvaluation, secondCoordinateMap]
    · simp [planeEvaluation, secondCoordinateMap]
  rw [← Category.assoc, hOrigin]
  apply pullback.hom_ext
  · rw [Category.assoc, planeChart_fst, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hFirst, polynomialChartMap_evaluation,
      graphPointMorphism_fst]
  · rw [Category.assoc, planeChart_snd, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hSecond, polynomialChartMap_evaluation,
      graphPointMorphism_snd]

/-- An actual translated open polynomial chart on the original projective product. -/
def translatedPlaneChart (p : ℕ) (a : k) : plane k ⟶ projectiveProduct k :=
  (planeTranslationIso a (a ^ p)).hom ≫ planeChart

instance translatedPlaneChart_isOpenImmersion (p : ℕ) (a : k) :
    IsOpenImmersion (translatedPlaneChart p a) := by
  unfold translatedPlaneChart
  infer_instance

@[reassoc] theorem translatedPlaneChart_structure (p : ℕ) (a : k) :
    translatedPlaneChart p a ≫ projectiveProductToSpec = planeStructure := by
  rw [translatedPlaneChart, Category.assoc, planeChart_structure,
    planeTranslationIso_hom_structure]

/-- Existing whole point-blowup stages can start at this actual selected graph point. -/
def translatedInitial (p : ℕ) (a : k) : PlaneChartedScheme k where
  carrier := projectiveProduct k
  structureMap := projectiveProductToSpec
  chart := translatedPlaneChart p a
  chart_isOpenImmersion := inferInstance
  chart_structure := translatedPlaneChart_structure p a

/-- The center morphism is exactly the existing rational graph-point morphism. -/
theorem translatedInitial_centerMorphism (p : ℕ) (a : k) :
    (translatedInitial p a).centerMorphism = graphPointMorphism p a :=
  origin_translated_productChart p a

/-- Its actual underlying center is the previously constructed closed graph point. -/
theorem translatedInitial_centerPoint (p : ℕ) (a : k) :
    (translatedInitial p a).chart.base originPoint = graphPoint p a := by
  rw [← (translatedInitial p a).centerMorphism_point,
    translatedInitial_centerMorphism]
  rfl

section Frobenius

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Frobenius additivity shows that the actual translated graph has the same local equation. -/
theorem coordinateTranslation_graphEquation (a : k) :
    coordinateTranslation a (a ^ p) (vCoord - uCoord ^ p) =
      (vCoord - uCoord ^ p : planeRing k) := by
  rw [map_sub, map_pow, coordinateTranslation_v, coordinateTranslation_u,
    add_pow_char, map_pow]
  ring

/-- The actual translated monomial parametrization agrees with translating its parameter. -/
theorem curveEvaluation_translation (a : k) :
    (Polynomial.evalRingHom (Polynomial.X ^ p : Polynomial k)).comp
        (coordinateTranslation a (a ^ p)).toRingHom =
      (parameterTranslation a).toRingHom.comp (Polynomial.evalRingHom (Polynomial.X ^ p)) := by
  apply Polynomial.ringHom_ext
  · intro f
    change (Polynomial.evalRingHom (Polynomial.X ^ p : Polynomial k))
      (coordinateTranslation a (a ^ p) (Polynomial.C f)) =
        parameterTranslation a ((Polynomial.evalRingHom (Polynomial.X ^ p : Polynomial k))
          (Polynomial.C f))
    rw [coordinateTranslation_C]
    simp
  · change (Polynomial.evalRingHom (Polynomial.X ^ p : Polynomial k))
      (coordinateTranslation a (a ^ p) (vCoord (k := k))) =
        parameterTranslation a ((Polynomial.evalRingHom (Polynomial.X ^ p : Polynomial k)) vCoord)
    rw [coordinateTranslation_v]
    simpa [vCoord, planeConstants, parameterTranslation] using
      (add_pow_char (Polynomial.X : Polynomial k) (Polynomial.C a) p).symm

/-- A genuine equality of scheme morphisms, obtained from the actual coordinate ring identity. -/
@[reassoc] theorem curveInPlane_translation (a : k) :
    curveInPlane (k := k) p ≫ (planeTranslationIso a (a ^ p)).hom =
      (parameterTranslationIso a).hom ≫ curveInPlane p := by
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (Polynomial.X ^ p : Polynomial k))) ≫
    Spec.map (CommRingCat.ofHom (coordinateTranslation a (a ^ p)).toRingHom) =
      Spec.map (CommRingCat.ofHom (parameterTranslation a).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (Polynomial.X ^ p)))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, curveEvaluation_translation]

/-- The local contact curve in the translated chart lies on the original whole Frobenius graph. -/
@[reassoc] theorem curveInPlane_translatedChart (a : k) :
    curveInPlane p ≫ translatedPlaneChart p a =
      (parameterTranslationIso a).hom ≫
        ProjectiveLineComparison.polynomialChartMap k 0 ≫ projectiveGraphMorphism p := by
  rw [translatedPlaneChart, ← Category.assoc, curveInPlane_translation, Category.assoc,
    curveInPlane_productChart]

/-- Every residual local curve in the translated whole-scheme tower maps
to the original Frobenius graph with its actual shifted parameter. -/
theorem translatedResidualCurve_toGraph (a : k) (n m : ℕ) (hm : m + n = p) :
    (translatedInitial p a).residualCurve n m ≫ (translatedInitial p a).toInitial n =
      (parameterTranslationIso a).hom ≫
        ProjectiveLineComparison.polynomialChartMap k 0 ≫ projectiveGraphMorphism p := by
  rw [PlaneChartedScheme.residualCurve_toInitial, hm]
  exact curveInPlane_translatedChart p a

end Frobenius

/-- Distinct actual affine parameters give distinct centers for these charts. -/
theorem translatedInitial_centers_injective [IsAlgClosed k] (p : ℕ) :
    Function.Injective (β := projectiveProduct k) (fun a : k =>
      (translatedInitial p a).chart.base (originPoint (k := k))) := by
  simpa only [translatedInitial_centerPoint] using graphPoint_injective (k := k) p

end KltDP.Examples.FrobeniusTranslatedCharts
