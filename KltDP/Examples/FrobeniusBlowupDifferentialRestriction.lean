import KltDP.Examples.FrobeniusBlowupDifferentialOverlapFrame
import KltDP.Examples.FrobeniusBlowupDifferentialOverlapSheaf

/-!
# Original differential restriction squares and overlap transition

The first-chart differential map is extended along the original chart-to-
overlap ring map. The pinned tensor cancellation equivalence identifies
its source with scalar extension along the original plane-to-overlap map.
The resulting composite with the original top restriction equals the
original base top differential map on the entire module.

The original left and right top restriction equivalences also determine
the actual transition between the two extended native chart top modules.
It sends the first native coordinate wedge to minus the original ratio
times the second native wedge. The induced tilde maps retain this square
and transition. No general tilde/pullback comparison or global differential
sheaf gluing is assumed or asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace KltDP.Examples.FrobeniusBlowupDifferentialRestriction

open FrobeniusBlowupContact FrobeniusBlowupDifferential FrobeniusBlowupDifferentialMap
open FrobeniusBlowupDifferentialOverlap FrobeniusBlowupDifferentialOverlapFrame
open KltDP.Geometry KltDP.Geometry.AffineBlowup

universe u

variable {k : Type u} [Field k]

local instance : Algebra (planeRing k) (reesChartRing k) :=
  FrobeniusBlowupDifferentialMap.chartBaseAlgebra
local instance : Algebra k (reesChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.leftFieldAlgebra
local instance : Algebra k (rightChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra
local instance : Algebra (planeRing k) (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra
local instance : Algebra k (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra
local instance : Algebra (reesChartRing k) (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapLeftAlgebra
local instance : Algebra (rightChartRing k) (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapRightAlgebra
local instance :
    @IsScalarTower k (planeRing k) (reesChartRing k)
      (inferInstance : SMul k (planeRing k))
      (FrobeniusBlowupDifferentialMap.chartBaseAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialMap.chartFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialMap.chartScalarTower (k := k)
local instance :
    @IsScalarTower k (planeRing k) (overlapRing k)
      (inferInstance : SMul k (planeRing k))
      (FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialOverlap.overlapPlaneTower (k := k)
local instance :
    @IsScalarTower k (reesChartRing k) (overlapRing k)
      (FrobeniusBlowupDifferentialOverlap.leftFieldAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapLeftAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialOverlap.overlapLeftTower (k := k)
local instance :
    @IsScalarTower k (rightChartRing k) (overlapRing k)
      (FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapRightAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialOverlap.overlapRightTower (k := k)

/-- The tower identity is the already proved equality of the original
plane-to-chart-to-overlap ring maps. -/
local instance :
    @IsScalarTower (planeRing k) (reesChartRing k) (overlapRing k)
      (FrobeniusBlowupDifferentialMap.chartBaseAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapLeftAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra (k := k)).toSMul :=
  @IsScalarTower.of_algebraMap_eq (planeRing k) (reesChartRing k) (overlapRing k)
    _ _ _ (FrobeniusBlowupDifferentialMap.chartBaseAlgebra (k := k))
    (FrobeniusBlowupDifferentialOverlap.overlapLeftAlgebra (k := k))
    (FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra (k := k)) fun r =>
      (conormalOverlapLeft_baseMap (centerIdeal (k := k)) centerU centerV r).symm

/-- The original plane top line, extended directly to the actual overlap. -/
abbrev baseModule (k : Type u) [Field k] : ModuleCat (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlapSheaf.sourceModule k

/-- The first native chart top module extended along its original overlap map. -/
abbrev leftModule (k : Type u) [Field k] : ModuleCat (overlapRing k) :=
  ModuleCat.of (overlapRing k)
    (overlapRing k ⊗[reesChartRing k] (⋀[reesChartRing k]^2 (ChartDifferential k)))

/-- The second native chart top module extended along the second original map. -/
abbrev rightModule (k : Type u) [Field k] : ModuleCat (overlapRing k) :=
  ModuleCat.of (overlapRing k)
    (overlapRing k ⊗[rightChartRing k] (⋀[rightChartRing k]^2 (RightDifferential k)))

/-- The existing chart differential map, preceded by the original canonical
comparison for the exterior square. -/
def planeChartTopMap :
    reesChartRing k ⊗[planeRing k] (⋀[planeRing k]^2 (PlaneDifferential k)) →ₗ[reesChartRing k]
      ⋀[reesChartRing k]^2 (ChartDifferential k) :=
  (chartTopDifferentialMap (k := k)).comp
    (KltDP.Compatibility.ExteriorPowerBaseChange.map
      (planeRing k) (reesChartRing k) 2 (PlaneDifferential k))

theorem planeChartTopMap_coordinate :
    planeChartTopMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) =
      chartU (k := k) • chartCoordinateTopForm (k := k) := by
  change chartTopDifferentialMap (k := k)
    (KltDP.Compatibility.ExteriorPowerBaseChange.map
      (planeRing k) (reesChartRing k) 2 (PlaneDifferential k)
      (1 ⊗ₜ[planeRing k] exteriorPower.ιMulti (planeRing k) 2
        ![KaehlerDifferential.D k (planeRing k) uCoord,
          KaehlerDifferential.D k (planeRing k) vCoord])) = _
  have hvec :
      (fun i : Fin 2 => (1 : reesChartRing k) ⊗ₜ[planeRing k]
        (![KaehlerDifferential.D k (planeRing k) uCoord,
          KaehlerDifferential.D k (planeRing k) vCoord] i)) =
      ![(1 : reesChartRing k) ⊗ₜ[planeRing k] KaehlerDifferential.D k (planeRing k) uCoord,
        (1 : reesChartRing k) ⊗ₜ[planeRing k] KaehlerDifferential.D k (planeRing k) vCoord] := by
    funext i
    fin_cases i <;> rfl
  exact (congrArg (chartTopDifferentialMap (k := k))
    (KltDP.Compatibility.ExteriorPowerBaseChange.map_one_tmul_ιMulti
      (planeRing k) (reesChartRing k) 2 (PlaneDifferential k)
      ![KaehlerDifferential.D k (planeRing k) uCoord,
        KaehlerDifferential.D k (planeRing k) vCoord])).trans
    ((congrArg (fun v : Fin 2 → ScalarExtendedPlaneDifferential k =>
      chartTopDifferentialMap (k := k) (exteriorPower.ιMulti (reesChartRing k) 2 v))
      hvec).trans (chartTopDifferentialMap_coordinate (k := k)))

/-- Actual scalar extension of the original chart map, with the canonical
tensor cancellation comparison on its source. -/
def planeChartOverlapMap : baseModule k →ₗ[overlapRing k] leftModule k :=
  ((planeChartTopMap (k := k)).baseChange (overlapRing k)).comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (planeRing k) (reesChartRing k) (overlapRing k) (overlapRing k)
      (⋀[planeRing k]^2 (PlaneDifferential k))).symm.toLinearMap

theorem planeChartOverlapMap_tmul (r : overlapRing k)
    (ω : ⋀[planeRing k]^2 (PlaneDifferential k)) :
    planeChartOverlapMap (k := k) (r ⊗ₜ[planeRing k] ω) =
      r ⊗ₜ[reesChartRing k] planeChartTopMap (k := k) (1 ⊗ₜ[planeRing k] ω) := by
  exact (congrArg ((planeChartTopMap (k := k)).baseChange (overlapRing k))
    (TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul
      (planeRing k) (reesChartRing k) (overlapRing k) r ω)).trans
    (LinearMap.baseChange_tmul (planeChartTopMap (k := k)) r (1 ⊗ₜ[planeRing k] ω))

theorem planeChartOverlapMap_coordinate :
    planeChartOverlapMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) =
      overlapU (k := k) • (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k)) := by
  letI : SMul (reesChartRing k) (overlapRing k) :=
    (FrobeniusBlowupDifferentialOverlap.overlapLeftAlgebra (k := k)).toSMul
  have hu : chartU (k := k) • (1 : overlapRing k) = overlapU (k := k) := by
    change overlapLeft (chartU (k := k)) * 1 = overlapU (k := k)
    exact (mul_one _).trans
      (conormalOverlapLeft_baseMap (centerIdeal (k := k)) centerU centerV uCoord)
  calc
    _ = (1 : overlapRing k) ⊗ₜ[reesChartRing k]
        planeChartTopMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) :=
      planeChartOverlapMap_tmul (k := k) 1 (coordinateTopForm (k := k))
    _ = (1 : overlapRing k) ⊗ₜ[reesChartRing k]
        (chartU (k := k) • chartCoordinateTopForm (k := k)) :=
      congrArg (fun z : ⋀[reesChartRing k]^2 (ChartDifferential k) =>
        (1 : overlapRing k) ⊗ₜ[reesChartRing k] z) (planeChartTopMap_coordinate (k := k))
    _ = (chartU (k := k) • (1 : overlapRing k)) ⊗ₜ[reesChartRing k]
        chartCoordinateTopForm (k := k) :=
      (TensorProduct.smul_tmul (R := reesChartRing k) (R' := reesChartRing k)
        (M := overlapRing k) (N := ⋀[reesChartRing k]^2 (ChartDifferential k))
        (chartU (k := k)) 1 (chartCoordinateTopForm (k := k))).symm
    _ = overlapU (k := k) ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k) :=
      congrArg (fun r : overlapRing k =>
        r ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k)) hu
    _ = overlapU (k := k) •
        (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k)) := by
      exact (congrArg (fun r : overlapRing k =>
        r ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k))
          (mul_one (overlapU (k := k))).symm).trans
        (TensorProduct.smul_tmul' (R := reesChartRing k) (R' := overlapRing k)
          (M := overlapRing k) (N := ⋀[reesChartRing k]^2 (ChartDifferential k))
          (overlapU (k := k)) (1 : overlapRing k)
          (chartCoordinateTopForm (k := k))).symm

/-- The actual plane-to-chart-to-overlap square commutes on the whole
original scalar-extended top line, not just on the coordinate wedge. -/
theorem leftTopMap_comp_planeChartOverlapMap :
    (leftTopMap (k := k)).comp (planeChartOverlapMap (k := k)) = baseTopMap (k := k) := by
  let f : baseModule k →ₗ[overlapRing k]
      FrobeniusBlowupDifferentialOverlapSheaf.targetModule k :=
    (leftTopMap (k := k)).comp (planeChartOverlapMap (k := k))
  have hc : f (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) =
      baseTopMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) :=
    (congrArg (leftTopMap (k := k)) (planeChartOverlapMap_coordinate (k := k))).trans
      (((leftTopMap (k := k)).map_smul (overlapU (k := k))
        (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k))).trans
        (baseTopMap_coordinate_left (k := k)).symm)
  change f = baseTopMap (k := k)
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r ω =>
      let c : overlapRing k :=
        r * algebraMap (planeRing k) (overlapRing k) (coordinateTopFormEvaluator ω)
      have hz := FrobeniusBlowupDifferentialOverlapSheaf.tensor_coordinate (k := k) r ω
      calc
        f (r ⊗ₜ[planeRing k] ω) =
            f (c • (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))) := congrArg f hz
        _ = c • f (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) := f.map_smul c _
        _ = c • baseTopMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) :=
          congrArg (fun w : FrobeniusBlowupDifferentialOverlapSheaf.targetModule k => c • w) hc
        _ = baseTopMap (k := k) (c • (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))) :=
          ((baseTopMap (k := k)).map_smul c _).symm
        _ = baseTopMap (k := k) (r ⊗ₜ[planeRing k] ω) :=
          congrArg (baseTopMap (k := k)) hz.symm
  | add x y hx hy =>
      exact (f.map_add x y).trans
        ((congrArg₂ (· + ·) hx hy).trans ((baseTopMap (k := k)).map_add x y).symm)

/-- The overlap transition is determined by the original two restrictions. -/
def chartTransition : leftModule k ≃ₗ[overlapRing k] rightModule k :=
  (leftTopEquiv (k := k)).trans (rightTopEquiv (k := k)).symm

theorem rightTopMap_chartTransition (z : leftModule k) :
    rightTopMap (k := k) (chartTransition (k := k) z) = leftTopMap (k := k) z :=
  (rightTopEquiv (k := k)).apply_symm_apply (leftTopEquiv (k := k) z)

theorem leftTopMap_chartTransition_symm (z : rightModule k) :
    leftTopMap (k := k) ((chartTransition (k := k)).symm z) = rightTopMap (k := k) z :=
  (leftTopEquiv (k := k)).apply_symm_apply (rightTopEquiv (k := k) z)

/-- The original first wedge has transition coefficient minus the actual
ratio T, relative to the original second wedge. -/
theorem chartTransition_coordinate :
    chartTransition (k := k) (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k)) =
      (-overlapT (k := k)) • (1 ⊗ₜ[rightChartRing k] rightChartForm (k := k)) := by
  apply (rightTopEquiv (k := k)).injective
  change rightTopMap (k := k)
      (chartTransition (k := k) (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k))) =
    rightTopMap (k := k)
      ((-overlapT (k := k)) • (1 ⊗ₜ[rightChartRing k] rightChartForm (k := k)))
  have hcoef : (-overlapT (k := k)) * (-overlapS (k := k)) = 1 :=
    (neg_mul_neg (overlapT (k := k)) (overlapS (k := k))).trans
      (overlapT_mul_overlapS (k := k))
  have hform : (-overlapT (k := k)) • rightForm (k := k) = leftForm (k := k) :=
    (congrArg (fun w : FrobeniusBlowupDifferentialOverlapSheaf.targetModule k =>
      (-overlapT (k := k)) • w) (rightForm_eq (k := k))).trans
      ((smul_smul (-overlapT (k := k)) (-overlapS (k := k)) (leftForm (k := k))).trans
        ((congrArg (fun r : overlapRing k => r • leftForm (k := k)) hcoef).trans
          (one_smul (overlapRing k) (leftForm (k := k)))))
  exact (rightTopMap_chartTransition (k := k) _).trans
    ((leftTopMap_coordinate (k := k)).trans
      (hform.symm.trans
        ((congrArg (fun w : FrobeniusBlowupDifferentialOverlapSheaf.targetModule k =>
          (-overlapT (k := k)) • w) (rightTopMap_coordinate (k := k)).symm).trans
          ((rightTopMap (k := k)).map_smul (-overlapT (k := k)) _).symm)))

theorem chartTransition_symm_coordinate :
    (chartTransition (k := k)).symm (1 ⊗ₜ[rightChartRing k] rightChartForm (k := k)) =
      (-overlapS (k := k)) • (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k)) := by
  apply (leftTopEquiv (k := k)).injective
  change leftTopMap (k := k)
      ((chartTransition (k := k)).symm (1 ⊗ₜ[rightChartRing k] rightChartForm (k := k))) =
    leftTopMap (k := k)
      ((-overlapS (k := k)) • (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k)))
  exact (leftTopMap_chartTransition_symm (k := k) _).trans
    ((rightTopMap_coordinate (k := k)).trans
      ((rightForm_eq (k := k)).trans
        ((congrArg (fun w : FrobeniusBlowupDifferentialOverlapSheaf.targetModule k =>
          (-overlapS (k := k)) • w) (leftTopMap_coordinate (k := k)).symm).trans
          ((leftTopMap (k := k)).map_smul (-overlapS (k := k)) _).symm)))

/-- The actual overlap transition induces an isomorphism of the original tildes. -/
def chartTransitionSheafIso : (leftModule k).tilde ≅ (rightModule k).tilde :=
  AffineModuleTilde.linearEquivIso (chartTransition (k := k))

theorem chartTransitionSheafIso_hom :
    (chartTransitionSheafIso (k := k)).hom =
      AffineModuleTilde.map (M := leftModule k) (N := rightModule k)
        (@ModuleCat.ofHom (overlapRing k) _ (leftModule k) (rightModule k)
          (leftModule k).isAddCommGroup (leftModule k).isModule
          (rightModule k).isAddCommGroup (rightModule k).isModule
          (chartTransition (k := k)).toLinearMap) := rfl

theorem chartTransitionSheafIso_hom_right :
    (chartTransitionSheafIso (k := k)).hom ≫ (rightTopSheafIso (k := k)).hom =
      (leftTopSheafIso (k := k)).hom := by
  let t : leftModule k ⟶ rightModule k :=
    @ModuleCat.ofHom (overlapRing k) _ (leftModule k) (rightModule k)
      (leftModule k).isAddCommGroup (leftModule k).isModule
      (rightModule k).isAddCommGroup (rightModule k).isModule
      (chartTransition (k := k)).toLinearMap
  let r : rightModule k ⟶ FrobeniusBlowupDifferentialOverlapSheaf.targetModule k :=
    @ModuleCat.ofHom (overlapRing k) _ (rightModule k)
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)
      (rightModule k).isAddCommGroup (rightModule k).isModule
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isAddCommGroup
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isModule
      (rightTopMap (k := k))
  let l : leftModule k ⟶ FrobeniusBlowupDifferentialOverlapSheaf.targetModule k :=
    @ModuleCat.ofHom (overlapRing k) _ (leftModule k)
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)
      (leftModule k).isAddCommGroup (leftModule k).isModule
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isAddCommGroup
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isModule
      (leftTopMap (k := k))
  have hc : t ≫ r = l := by
    apply ModuleCat.hom_ext
    change (rightTopMap (k := k)).comp (chartTransition (k := k)).toLinearMap =
      leftTopMap (k := k)
    apply LinearMap.ext
    intro z
    exact rightTopMap_chartTransition (k := k) z
  have ht : (chartTransitionSheafIso (k := k)).hom = AffineModuleTilde.map t :=
    chartTransitionSheafIso_hom (k := k)
  have hr : (rightTopSheafIso (k := k)).hom = AffineModuleTilde.map r :=
    rightTopSheafIso_hom (k := k)
  have hl : (leftTopSheafIso (k := k)).hom = AffineModuleTilde.map l :=
    leftTopSheafIso_hom (k := k)
  calc
    _ = AffineModuleTilde.map t ≫ AffineModuleTilde.map r :=
      congrArg₂
        (fun (f : (leftModule k).tilde ⟶ (rightModule k).tilde)
          (g : (rightModule k).tilde ⟶
            (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).tilde) => f ≫ g)
        ht hr
    _ = AffineModuleTilde.map (t ≫ r) := (AffineModuleTilde.map_comp t r).symm
    _ = AffineModuleTilde.map l :=
      congrArg (AffineModuleTilde.map (M := leftModule k)
        (N := FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)) hc
    _ = (leftTopSheafIso (k := k)).hom := hl.symm

/-- The first-chart factorization also retains its original tilde map. -/
def planeChartOverlapSheafMap : (baseModule k).tilde ⟶ (leftModule k).tilde :=
  AffineModuleTilde.map (ModuleCat.ofHom (planeChartOverlapMap (k := k)))

theorem planeChartOverlapSheafMap_comp :
    planeChartOverlapSheafMap (k := k) ≫ (leftTopSheafIso (k := k)).hom =
      FrobeniusBlowupDifferentialOverlapSheaf.baseTopSheafMap (k := k) := by
  let b : baseModule k ⟶ leftModule k :=
    @ModuleCat.ofHom (overlapRing k) _ (baseModule k) (leftModule k)
      (baseModule k).isAddCommGroup (baseModule k).isModule
      (leftModule k).isAddCommGroup (leftModule k).isModule
      (planeChartOverlapMap (k := k))
  let l : leftModule k ⟶ FrobeniusBlowupDifferentialOverlapSheaf.targetModule k :=
    @ModuleCat.ofHom (overlapRing k) _ (leftModule k)
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)
      (leftModule k).isAddCommGroup (leftModule k).isModule
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isAddCommGroup
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isModule
      (leftTopMap (k := k))
  let d : baseModule k ⟶ FrobeniusBlowupDifferentialOverlapSheaf.targetModule k :=
    @ModuleCat.ofHom (overlapRing k) _ (baseModule k)
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)
      (baseModule k).isAddCommGroup (baseModule k).isModule
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isAddCommGroup
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isModule
      (baseTopMap (k := k))
  have hc : b ≫ l = d := by
    apply ModuleCat.hom_ext
    change (leftTopMap (k := k)).comp (planeChartOverlapMap (k := k)) =
      baseTopMap (k := k)
    exact leftTopMap_comp_planeChartOverlapMap (k := k)
  have hl : (leftTopSheafIso (k := k)).hom = AffineModuleTilde.map l :=
    leftTopSheafIso_hom (k := k)
  rw [hl]
  change AffineModuleTilde.map b ≫ AffineModuleTilde.map l = AffineModuleTilde.map d
  exact (AffineModuleTilde.map_comp b l).symm.trans
    (congrArg (AffineModuleTilde.map (M := baseModule k)
      (N := FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)) hc)

/-- Canonical sections on every actual overlap open retain the original
transition coefficient; these are the original tilde section maps. -/
theorem chartTransitionSheafIso_coordinate (U : Opens (PrimeSpectrum (overlapRing k))) :
    (chartTransitionSheafIso (k := k)).hom.val.app (op U)
      (ModuleCat.Tilde.toOpen (leftModule k) U
        (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k))) =
      ModuleCat.Tilde.toOpen (rightModule k) U
        ((-overlapT (k := k)) • (1 ⊗ₜ[rightChartRing k] rightChartForm (k := k))) := by
  let t : leftModule k ⟶ rightModule k :=
    @ModuleCat.ofHom (overlapRing k) _ (leftModule k) (rightModule k)
      (leftModule k).isAddCommGroup (leftModule k).isModule
      (rightModule k).isAddCommGroup (rightModule k).isModule
      (chartTransition (k := k)).toLinearMap
  have ht : (chartTransitionSheafIso (k := k)).hom = AffineModuleTilde.map t :=
    chartTransitionSheafIso_hom (k := k)
  have hc : t (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k)) =
      (-overlapT (k := k)) • (1 ⊗ₜ[rightChartRing k] rightChartForm (k := k)) := by
    change chartTransition (k := k)
        (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k)) = _
    exact chartTransition_coordinate (k := k)
  exact (congrArg
    (fun f : (leftModule k).tilde ⟶ (rightModule k).tilde =>
      f.val.app (op U) (ModuleCat.Tilde.toOpen (leftModule k) U
        (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k)))) ht).trans
    ((AffineModuleTilde.map_app_toOpen t U
      (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k))).trans
      (congrArg (ModuleCat.Tilde.toOpen (rightModule k) U) hc))

end KltDP.Examples.FrobeniusBlowupDifferentialRestriction
