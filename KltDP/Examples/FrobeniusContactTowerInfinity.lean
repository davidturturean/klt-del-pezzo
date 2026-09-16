import KltDP.Examples.FrobeniusGraphPicardClassPowerCharts
import KltDP.Examples.FrobeniusGlobalBlowupSmooth
import KltDP.Examples.FrobeniusStageComplement
import KltDP.Examples.FrobeniusGraphPicardClassMixedOverlap
import KltDP.Examples.FrobeniusTranslatedCharts
import KltDP.Examples.FrobeniusGraphRationalPoints

/-!
# The contact-blowup tower at the point at infinity

The manuscript treats the point `(∞, ∞)` of the Frobenius graph by the reciprocal coordinates
`u = 1/x`, `v = 1/y`, in which the graph has again the equation `v = u^p`. In the accepted
library this chart is the actual product chart `productChart 1 1` of `P¹ ×_k P¹` (the product of
the two second standard charts), and `curveInPlane_diagonalChart p 1` proves that the monomial
curve `v = u^p` in that chart is the restriction of the whole graph morphism.

This module packages that chart as accepted initial data `infinityInitial : PlaneChartedScheme k`
(carrier `P¹ ×_k P¹`, chart `productChart 1 1`, centre the origin of the reciprocal chart, i.e.
the point `([0:1],[0:1])`), so that every accepted result about `PlaneChartedScheme` towers applies
verbatim: the whole scheme after `n` blowups at `(∞,∞)`, its proper projection, properness and
smoothness of relative dimension two of every stage, the complement isomorphism, and the fact
that the residual curve with accumulated exponent `p` projects onto the whole graph. No
characteristic assumption is needed for the last statement, because the reciprocal equation is the
same monomial for every exponent.

The centre at infinity is shown to differ from every finite selected centre `(a, a^p)`: its first
projection lies outside the first standard chart, while `[1:a]` lies inside it. Nothing is
transported through an automorphism; the results are the accepted generic theorems specialised
to accepted initial data.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusContactTowerInfinity

open KltDP.Geometry ProjectiveLineComparison FrobeniusProjectivePoints
  FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
  FrobeniusProductPlaneChart FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupSmooth
  FrobeniusGraphClosed FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassPowerCharts
  FrobeniusGraphPicardClassMixedOverlap FrobeniusStageComplement.PlaneChartedScheme

variable {k : Type u} [Field k]

/-- Every product chart preserves the coefficient-field structure morphism. -/
@[reassoc] theorem productChart_structure (i j : Fin 2) :
    productChart (k := k) i j ≫ projectiveProductToSpec = planeStructure := by
  rw [projectiveProductToSpec, ← Category.assoc, productChart_fst,
    Category.assoc, polynomialChartMap_structureMap, ← Spec.map_comp]
  rfl

/-- The reciprocal chart `u = 1/x, v = 1/y` as accepted initial data for the blowup recursion. -/
def infinityInitial (k : Type u) [Field k] : PlaneChartedScheme k where
  carrier := projectiveProduct k
  structureMap := projectiveProductToSpec
  chart := productChart 1 1
  chart_isOpenImmersion := inferInstance
  chart_structure := productChart_structure 1 1

/-- The whole scheme after `n` contact blowups at `(∞,∞)`. -/
abbrev infinityStage (n : ℕ) : Scheme.{u} := ((infinityInitial k).stage n).carrier

/-- Its composite projection to the projective product. -/
def infinityProjection (n : ℕ) : infinityStage (k := k) n ⟶ projectiveProduct k :=
  (infinityInitial k).toInitial n

instance infinityProjection_isProper (n : ℕ) : IsProper (infinityProjection (k := k) n) :=
  (infinityInitial k).toInitial_isProper n

instance infinityInitial_structure_isProper : IsProper (infinityInitial k).structureMap :=
  projectiveProductInitial_structure_isProper

instance infinityStage_structure_isProper (n : ℕ) :
    IsProper ((infinityInitial k).stage n).structureMap :=
  (infinityInitial k).stageStructure_isProper n

instance infinityInitial_structure_smoothTwo :
    IsSmoothOfRelativeDimension 2 (infinityInitial k).structureMap :=
  projectiveProduct_structure_smoothTwo

instance infinityStage_structure_smoothTwo (n : ℕ) :
    IsSmoothOfRelativeDimension 2 ((infinityInitial k).stage n).structureMap :=
  ExplicitStages.stageStructure_smoothTwo (infinityInitial k) n

instance infinityStage_structure_smooth (n : ℕ) :
    IsSmooth ((infinityInitial k).stage n).structureMap :=
  IsSmoothOfRelativeDimension.isSmooth 2 _

theorem infinityProjection_structure (n : ℕ) :
    infinityProjection (k := k) n ≫ projectiveProductToSpec =
      ((infinityInitial k).stage n).structureMap :=
  (infinityInitial k).toInitial_structure n

/-- The centre at infinity: the origin of the reciprocal chart, i.e. `([0:1],[0:1])`. -/
def infinityCenter (k : Type u) [Field k] : projectiveProduct k :=
  (productChart 1 1).base (originPoint (k := k))

theorem infinityCenter_isClosed : IsClosed ({infinityCenter k} : Set (projectiveProduct k)) :=
  (infinityInitial k).center_closed

/-- Every stage centre projects to the centre at infinity. -/
theorem infinityStage_center_projection (n : ℕ) :
    (infinityProjection n).base (((infinityInitial k).stage n).chart.base (originPoint (k := k))) =
      infinityCenter k :=
  centerPoint_toInitial (infinityInitial k) n

/-- The finite projection is an isomorphism over the complement of the centre at infinity. -/
def infinityComplementIso (n : ℕ) :
    (stagePuncture (infinityInitial k) n).toScheme ≅ (initialPuncture (infinityInitial k)).toScheme :=
  stageComplementIso (infinityInitial k) n

/-- The reciprocal-chart residual curve with accumulated exponent `p` projects onto the whole
Frobenius graph, for every exponent and every field. -/
theorem infinityResidualCurve_toGraph (p n m : ℕ) (hm : m + n = p) :
    (infinityInitial k).residualCurve n m ≫ infinityProjection n =
      polynomialChartMap k 1 ≫ FrobeniusProjectiveMorphism.projectiveGraphMorphism p := by
  rw [infinityProjection, PlaneChartedScheme.residualCurve_toInitial, hm]
  exact curveInPlane_diagonalChart p 1

/-- Before the contact is exhausted, the next centre lies on the residual curve. -/
theorem infinity_center_on_residualCurve (n m : ℕ) (hm : 0 < m) :
    parameterOriginMorphism (k := k) ≫ (infinityInitial k).residualCurve n m =
      ((infinityInitial k).stage n).centerMorphism :=
  (infinityInitial k).parameterOrigin_residualCurve n m hm

/-- The first projection of the centre at infinity lies outside the first standard chart. -/
theorem infinityCenter_fst_not_mem_chartOpen :
    (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base (infinityCenter k) ∉
      chartOpen k 0 := by
  have h : (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base
      (infinityCenter k) =
      (polynomialChartMap k 1).base
        ((Spec.map (CommRingCat.ofHom (firstCoordinateMap (k := k)))).base originPoint) := by
    change (productChart 1 1 ≫
      pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base originPoint = _
    rw [productChart_fst]
    rfl
  rw [h]
  have hiff := polynomialChart_mem_other_iff (k := k) 1
    ((Spec.map (CommRingCat.ofHom (firstCoordinateMap (k := k)))).base originPoint)
  have hother : otherIndex (1 : Fin 2) = 0 := Equiv.swap_apply_right 0 1
  rw [hother] at hiff
  rw [hiff]
  intro hX
  apply hX
  change firstCoordinateMap (Polynomial.X : Polynomial k) ∈ centerIdeal
  exact Ideal.subset_span (Or.inl rfl)

/-- The finite selected centres lie in the first standard chart. -/
theorem graphPoint_fst_mem_chartOpen (p : ℕ) (a : k) :
    (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base (graphPoint p a) ∈
      chartOpen k 0 := by
  rw [graphPoint_fst, ← polynomialChartMap_opensRange k 0]
  refine ⟨(Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))).base
    (IsLocalRing.closedPoint k), ?_⟩
  change (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫ polynomialChartMap k 0).base
    (IsLocalRing.closedPoint k) = point a
  rw [FrobeniusTranslatedCharts.polynomialChartMap_evaluation]
  rfl

/-- The centre at infinity is distinct from every finite selected centre. -/
theorem infinityCenter_ne_graphPoint (p : ℕ) (a : k) : infinityCenter k ≠ graphPoint p a := by
  intro h
  apply infinityCenter_fst_not_mem_chartOpen (k := k)
  rw [h]
  exact graphPoint_fst_mem_chartOpen p a

end KltDP.Examples.FrobeniusContactTowerInfinity
