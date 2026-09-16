import KltDP.Examples.FrobeniusBlowupChartIteration
import KltDP.Examples.FrobeniusProductPlaneChart
import KltDP.Geometry.PointBlowupProper
import KltDP.Geometry.ProjectiveProper

/-!
# Entire finite point-blowup stages along the selected contact chart

The initial data are an actual scheme over `k` and an actual polynomial-plane
open chart over `k`. At each step the origin is proved to be a closed rational
point in the entire scheme. The whole next scheme is constructed by gluing
the actual Rees point blowup to the unchanged complement. Its next plane
chart is the already proved Rees chart, followed by the gluing inclusion.

The recursion constructs entire schemes, their proper projections, and
actual local residual-curve morphisms for every finite number of steps.
The original projective product supplies concrete initial data through its
proved product-plane chart. No smooth-coordinate theorem for an arbitrary
surface is assumed. These results do not identify global strict-transform
closures or prove their intersection numbers or the final contraction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGlobalBlowupStages

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupSmooth

variable {k : Type u} [Field k]

/-- The selected spectrum point has the already proved maximal center ideal. -/
local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The actual origin morphism preserves the original coefficient field. -/
theorem originMorphism_structure :
    originMorphism (k := k) ≫ planeStructure = 𝟙 (Spec (CommRingCat.of k)) := by
  have h : (originEvaluation (k := k)).comp planeConstants = RingHom.id k := by
    apply RingHom.ext
    intro r
    simp [originEvaluation, planeConstants]
  rw [originMorphism, planeStructure, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, h, CommRingCat.ofHom_id, Spec.map_id]

/-- The selected actual blowup chart projection fixes the original field. -/
theorem coordinateBlowdown_structure :
    coordinateBlowdown (k := k) ≫ planeStructure = planeStructure := by
  have h : (chartSubstitution (k := k)).comp planeConstants = planeConstants := by
    apply RingHom.ext
    intro r
    exact chartSubstitution_C (Polynomial.C r)
  rw [coordinateBlowdown_eq, planeStructure, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, h]

/-- Input geometric data: a scheme, its field structure, and an actual open
polynomial-plane chart over that field. Closed centers, blowups, properness
and residual-curve identities are derived below, not included as fields. -/
structure PlaneChartedScheme (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (CommRingCat.of k)
  chart : plane k ⟶ carrier
  chart_isOpenImmersion : IsOpenImmersion chart
  chart_structure : chart ≫ structureMap = planeStructure

instance (A : PlaneChartedScheme k) : IsOpenImmersion A.chart :=
  A.chart_isOpenImmersion

namespace PlaneChartedScheme

variable (A : PlaneChartedScheme k)

/-- The actual rational center in the entire current scheme. -/
def centerMorphism : Spec (CommRingCat.of k) ⟶ A.carrier :=
  originMorphism ≫ A.chart

@[simp] theorem centerMorphism_structure :
    A.centerMorphism ≫ A.structureMap = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [centerMorphism, Category.assoc, A.chart_structure, originMorphism_structure]

/-- The point selected in the whole scheme is exactly the image of the
actual maximal origin ideal in the polynomial chart. -/
theorem centerMorphism_point :
    fieldMorphismPoint A.centerMorphism = A.chart.base (originPoint (k := k)) := by
  change A.chart.base (fieldMorphismPoint (originMorphism (k := k))) = _
  rw [originMorphism_point]

/-- Closedness in the whole scheme follows from the actual rational section. -/
theorem center_closed : IsClosed ({A.chart.base (originPoint (k := k))} : Set A.carrier) := by
  rw [← A.centerMorphism_point]
  exact isClosed_point_of_section A.structureMap A.centerMorphism A.centerMorphism_structure

/-- Replace the entire chosen affine neighborhood by its actual Rees blowup,
and glue it to the unchanged complement of the derived closed point. -/
abbrev nextScheme : Scheme.{u} :=
  PointBlowupGluing.scheme A.chart (originPoint (k := k)) A.center_closed

/-- The actual global one-step blowup projection. -/
def nextProjection : A.nextScheme ⟶ A.carrier :=
  PointBlowupGluing.projection A.chart (originPoint (k := k)) A.center_closed

/-- The complete affine Rees blowup embeds into the new global scheme. -/
def nextAffineBlowup : AffineBlowup.scheme (centerIdeal (k := k)) ⟶ A.nextScheme :=
  PointBlowupGluing.affineBlowupι A.chart (originPoint (k := k)) A.center_closed

instance nextAffineBlowup_isOpenImmersion : IsOpenImmersion A.nextAffineBlowup := by
  unfold nextAffineBlowup
  infer_instance

@[reassoc] theorem nextAffineBlowup_projection :
    A.nextAffineBlowup ≫ A.nextProjection = AffineBlowup.toSpec centerIdeal ≫ A.chart :=
  PointBlowupGluing.affineBlowupι_projection A.chart (originPoint (k := k)) A.center_closed

/-- The next chart is the actual first Rees chart followed by the actual
open inclusion of the affine blowup into the entire new scheme. -/
def nextChart : plane k ⟶ A.nextScheme := coordinateChart ≫ A.nextAffineBlowup

instance nextChart_isOpenImmersion : IsOpenImmersion A.nextChart := by
  unfold nextChart
  infer_instance

@[reassoc] theorem nextChart_projection :
    A.nextChart ≫ A.nextProjection = coordinateBlowdown ≫ A.chart := by
  rw [nextChart, Category.assoc, nextAffineBlowup_projection, ← Category.assoc]
  rfl

/-- The next scheme's field structure is the composite of the actual
projection and the previous field structure. -/
def nextStructure : A.nextScheme ⟶ Spec (CommRingCat.of k) :=
  A.nextProjection ≫ A.structureMap

theorem nextChart_structure : A.nextChart ≫ A.nextStructure = planeStructure := by
  rw [nextStructure, ← Category.assoc, nextChart_projection,
    Category.assoc, A.chart_structure, coordinateBlowdown_structure]

/-- A whole next stage with its derived actual coordinate chart. -/
def next : PlaneChartedScheme k where
  carrier := A.nextScheme
  structureMap := A.nextStructure
  chart := A.nextChart
  chart_isOpenImmersion := inferInstance
  chart_structure := A.nextChart_structure

/-- The actual point-blowup projection is proper because its actual
polynomial-plane center ideal is finitely generated. -/
instance nextProjection_isProper : IsProper A.nextProjection := by
  unfold nextProjection
  infer_instance

/-- Every natural number gives an entire iterated scheme, not just a
repeated abstract local chart. -/
def stage : ℕ → PlaneChartedScheme k
  | 0 => A
  | n + 1 => (stage n).next

/-- The actual projection from stage `n+1` to stage `n`. -/
def stepProjection (n : ℕ) : (A.stage (n + 1)).carrier ⟶ (A.stage n).carrier :=
  (A.stage n).nextProjection

instance stepProjection_isProper (n : ℕ) : IsProper (A.stepProjection n) :=
  (A.stage n).nextProjection_isProper

/-- The morphism to the initial whole scheme is constructed by composing
the actual global one-step blowup projections. -/
def toInitial : (n : ℕ) → ((A.stage n).carrier ⟶ A.carrier)
  | 0 => 𝟙 A.carrier
  | n + 1 => A.stepProjection n ≫ toInitial n

@[simp] theorem toInitial_zero : A.toInitial 0 = 𝟙 A.carrier := rfl

@[simp] theorem toInitial_succ (n : ℕ) :
    A.toInitial (n + 1) = A.stepProjection n ≫ A.toInitial n := rfl

/-- Every finite composite projection is proper. -/
instance toInitial_isProper (n : ℕ) : IsProper (A.toInitial n) := by
  induction n with
  | zero => change IsProper (𝟙 A.carrier); infer_instance
  | succ n ih =>
      letI : IsProper (A.toInitial n) := ih
      rw [toInitial_succ]
      infer_instance

/-- The recursive field structure agrees with the actual projection to
the initial scheme. -/
theorem toInitial_structure (n : ℕ) :
    A.toInitial n ≫ A.structureMap = (A.stage n).structureMap := by
  induction n with
  | zero => exact Category.id_comp _
  | succ n ih =>
      rw [toInitial_succ, Category.assoc, ih]
      rfl

/-- If the actual initial structure morphism is proper, each constructed
whole stage is proper over the same original field. -/
instance stageStructure_isProper [IsProper A.structureMap] (n : ℕ) :
    IsProper (A.stage n).structureMap := by
  rw [← A.toInitial_structure n]
  infer_instance

/-- The global projection restricted to the actual selected open chart is
exactly the previously constructed local sequence of Rees chart maps. -/
@[reassoc] theorem stage_chart_toInitial (n : ℕ) :
    (A.stage n).chart ≫ A.toInitial n = stageProjection n ≫ A.chart := by
  induction n with
  | zero => simp [stage, stageProjection, toInitial]
  | succ n ih =>
      rw [toInitial_succ, ← Category.assoc]
      change ((A.stage n).nextChart ≫ (A.stage n).nextProjection) ≫ A.toInitial n = _
      rw [nextChart_projection, Category.assoc, ih, ← Category.assoc]
      rfl

/-- The residual polynomial curve is an actual morphism into the entire
stage through its derived coordinate open chart. -/
def residualCurve (n m : ℕ) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ (A.stage n).carrier :=
  curveInPlane m ≫ (A.stage n).chart

/-- At the next stage this morphism factors through the actual residual
closed curve of the local Rees point blowup. -/
theorem residualCurve_succ (n m : ℕ) :
    A.residualCurve (n + 1) m =
      residualCurveMorphism m ≫ (A.stage n).nextAffineBlowup := by
  change curveInPlane m ≫ (coordinateChart ≫ (A.stage n).nextAffineBlowup) = _
  rw [← Category.assoc, curveInPlane_intoBlowup]

/-- In the positive-contact range used in the manuscript, the next
center lies on the actual residual curve. -/
theorem parameterOrigin_residualCurve (n m : ℕ) (hm : 0 < m) :
    parameterOriginMorphism (k := k) ≫ A.residualCurve n m =
      (A.stage n).centerMorphism := by
  rw [residualCurve, ← Category.assoc, parameterOrigin_curveInPlane m hm]
  rfl

/-- The actual finite-stage residual curve projects to the original
monomial curve with the accumulated contact exponent. -/
@[reassoc] theorem residualCurve_toInitial (n m : ℕ) :
    A.residualCurve n m ≫ A.toInitial n = curveInPlane (m + n) ≫ A.chart := by
  rw [residualCurve, Category.assoc, stage_chart_toInitial,
    ← Category.assoc, curveInPlane_stageProjection]

/-- The terminal residual equation is `v=1`; its actual global morphism
projects to the original exponent-`p` monomial curve. -/
theorem terminal_residualCurve_toInitial (p : ℕ) :
    A.residualCurve p 0 ≫ A.toInitial p = curveInPlane p ≫ A.chart := by
  simpa only [Nat.zero_add] using A.residualCurve_toInitial p 0

end PlaneChartedScheme

/-- Concrete initial data: the actual product of two projective lines,
with its derived polynomial-plane open chart over the original field. -/
def projectiveProductInitial : PlaneChartedScheme k where
  carrier := FrobeniusProjectivePoints.projectiveProduct k
  structureMap := FrobeniusProjectivePoints.projectiveProductToSpec
  chart := FrobeniusProductPlaneChart.planeChart
  chart_isOpenImmersion := inferInstance
  chart_structure := FrobeniusProductPlaneChart.planeChart_structure

instance projectiveProductInitial_structure_isProper :
    IsProper (projectiveProductInitial (k := k)).structureMap := by
  change IsProper (FrobeniusProjectivePoints.projectiveProductToSpec (k := k))
  unfold FrobeniusProjectivePoints.projectiveProductToSpec
  letI : IsProper (Limits.pullback.fst
      (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)) :=
    MorphismProperty.pullback_fst (P := @IsProper)
      (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) inferInstance
  infer_instance

/-- The entire finite sequence begins on the actual projective product. -/
abbrev projectiveContactStage (n : ℕ) : Scheme.{u} :=
  ((projectiveProductInitial (k := k)).stage n).carrier

/-- The actual composite projection to the original projective product. -/
def projectiveContactProjection (n : ℕ) :
    projectiveContactStage (k := k) n ⟶ FrobeniusProjectivePoints.projectiveProduct k :=
  (projectiveProductInitial (k := k)).toInitial n

instance projectiveContactProjection_isProper (n : ℕ) :
    IsProper (projectiveContactProjection (k := k) n) :=
  (projectiveProductInitial (k := k)).toInitial_isProper n

/-- Every whole contact stage constructed from the projective product is
proper over the original coefficient field. -/
instance projectiveContactStage_structure_isProper (n : ℕ) :
    IsProper ((projectiveProductInitial (k := k)).stage n).structureMap :=
  (projectiveProductInitial (k := k)).stageStructure_isProper n

end KltDP.Examples.FrobeniusGlobalBlowupStages
