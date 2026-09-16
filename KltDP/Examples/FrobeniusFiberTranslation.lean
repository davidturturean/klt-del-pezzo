import KltDP.Examples.FrobeniusFiberClosure
import KltDP.Examples.FrobeniusTranslatedCharts
import KltDP.Examples.FrobeniusGraphPicardClassZeroFiber

/-!
# The tangent fibre of the translated chart is the horizontal fibre at height `a^p`

The fibre `v = 0` of the polynomial plane, transported through the translated chart at `(a, a^p)`,
is the horizontal fibre `{y = a^p}` of `P¹ ×_k P¹` restricted to the affine parameter line, with the
parameter shifted by `a` (`fiberCurve_translatedChart`). This is the fibre analogue of the accepted
`curveInPlane_translatedChart`, and it is what identifies the generic strict fibre of a translated
tower with the strict transform of the whole horizontal fibre.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusFiberTranslation

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusBlowupContact FrobeniusBlowupChartIteration
  FrobeniusProductPlaneChart FrobeniusTranslatedCharts FrobeniusGraphPicardClassZeroFiber
  FrobeniusFiberClosure FrobeniusBlowupSmooth

variable {k : Type u} [Field k]

/-- The horizontal line `v = b` of the polynomial plane, parametrised by `u = t`. -/
def fiberCurveAt (b : k) : Spec (CommRingCat.of (Polynomial k)) ⟶ plane k :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (Polynomial.C b : Polynomial k)))

/-- Translating `u ↦ u + a`, `v ↦ v + b` carries the fibre `v = 0` to the fibre `v = b`. -/
theorem fiberEvaluation_translation (a b : k) :
    (Polynomial.evalRingHom (0 : Polynomial k)).comp (coordinateTranslation a b).toRingHom =
      (parameterTranslation a).toRingHom.comp
        (Polynomial.evalRingHom (Polynomial.C b : Polynomial k)) := by
  apply Polynomial.ringHom_ext
  · intro f
    change Polynomial.evalRingHom (0 : Polynomial k) (coordinateTranslation a b (Polynomial.C f)) =
      parameterTranslation a (Polynomial.evalRingHom (Polynomial.C b : Polynomial k)
        (Polynomial.C f))
    rw [coordinateTranslation_C]
    simp
  · change Polynomial.evalRingHom (0 : Polynomial k) (coordinateTranslation a b (vCoord (k := k))) =
      parameterTranslation a (Polynomial.evalRingHom (Polynomial.C b : Polynomial k) vCoord)
    rw [coordinateTranslation_v, map_add]
    simp [parameterTranslation, vCoord, planeConstants]

@[reassoc] theorem fiberCurve_translation (a b : k) :
    fiberCurve (k := k) ≫ (planeTranslationIso a b).hom =
      (parameterTranslationIso a).hom ≫ fiberCurveAt b := by
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Polynomial k))) ≫
    Spec.map (CommRingCat.ofHom (coordinateTranslation a b).toRingHom) =
      Spec.map (CommRingCat.ofHom (parameterTranslation a).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (Polynomial.C b : Polynomial k)))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, fiberEvaluation_translation]

theorem fiberCurveAt_firstCoordinate (b : k) :
    fiberCurveAt b ≫ Spec.map (CommRingCat.ofHom firstCoordinateMap) =
      𝟙 (Spec (CommRingCat.of (Polynomial k))) := by
  have h : (Polynomial.evalRingHom (Polynomial.C b : Polynomial k)).comp
      firstCoordinateMap = RingHom.id (Polynomial k) := by
    apply RingHom.ext
    intro f
    simp [firstCoordinateMap]
  rw [fiberCurveAt, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h, CommRingCat.ofHom_id,
    Spec.map_id]

theorem fiberCurveAt_secondCoordinate (b : k) :
    fiberCurveAt b ≫ Spec.map (CommRingCat.ofHom secondCoordinateMap) =
      Spec.map (CommRingCat.ofHom
        ((Polynomial.C : k →+* Polynomial k).comp (Polynomial.evalRingHom b))) := by
  have h : (Polynomial.evalRingHom (Polynomial.C b : Polynomial k)).comp
      secondCoordinateMap = (Polynomial.C : k →+* Polynomial k).comp (Polynomial.evalRingHom b) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [secondCoordinateMap]
    · simp [secondCoordinateMap]
  rw [fiberCurveAt, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- The line `v = b` of the product plane chart is the horizontal fibre at height `b`. -/
@[reassoc] theorem fiberCurveAt_planeChart (b : k) :
    fiberCurveAt b ≫ planeChart =
      ProjectiveLineComparison.polynomialChartMap k 0 ≫ horizontalFiberMorphism b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, horizontalFiberMorphism, pullback.lift_fst, Category.comp_id]
    rw [planeChart_fst, ← Category.assoc, fiberCurveAt_firstCoordinate, Category.id_comp]
  · simp only [Category.assoc, horizontalFiberMorphism, pullback.lift_snd]
    rw [planeChart_snd, ← Category.assoc, fiberCurveAt_secondCoordinate, ← Category.assoc,
      ProjectiveLineComparison.polynomialChartMap_structureMap, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, polynomialChartMap_evaluation]

/-- The tangent fibre of the translated chart at `(a, a^p)` is the horizontal fibre at height `a^p`. -/
@[reassoc] theorem fiberCurve_translatedChart (p : ℕ) (a : k) :
    fiberCurve ≫ translatedPlaneChart p a =
      (parameterTranslationIso a).hom ≫ ProjectiveLineComparison.polynomialChartMap k 0 ≫
        horizontalFiberMorphism (a ^ p) := by
  rw [translatedPlaneChart, ← Category.assoc, fiberCurve_translation, Category.assoc,
    fiberCurveAt_planeChart]

end KltDP.Examples.FrobeniusFiberTranslation
