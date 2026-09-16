import KltDP.Examples.FrobeniusReesChartDifferentialFrame
import KltDP.Compatibility.ExteriorPowerBaseChange
import KltDP.Geometry.AffineBlowupExceptionalOverlap
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Original differential maps on the actual two-chart intersection

The overlap is the original homogeneous product localization whose two
maps are already identified with the categorical Rees-chart projections.
The field and chart algebra structures use those original ring maps.

The two reciprocal ratios give the actual differential transition
`dV ∧ dS = -S • (dU ∧ dT)`. The original base two-form therefore has
the same value in both coordinate descriptions on this same overlap.
No arbitrary overlap, transition formula or canonical-divisor conclusion
is supplied as an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace KltDP.Examples.FrobeniusBlowupDifferentialOverlap

open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupDifferential
open FrobeniusBlowupDifferentialMap
open KltDP.Geometry KltDP.Geometry.AffineBlowup

universe u

section Wedge

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

private theorem wedge_add_left (x y z : M) :
    wedgeTwo (A := A) (x + y) z = wedgeTwo x z + wedgeTwo y z :=
  (exteriorPower.ιMulti A 2).map_vecCons_add ![z] x y

private theorem wedge_smul_left (c : A) (x y : M) :
    wedgeTwo (A := A) (c • x) y = c • wedgeTwo x y :=
  (exteriorPower.ιMulti A 2).map_vecCons_smul ![y] c x

private theorem wedge_smul_right (c : A) (x y : M) :
    wedgeTwo (A := A) x (c • y) = c • wedgeTwo x y :=
  ((exteriorPower.ιMulti A 2).curryLeft x).map_vecCons_smul ![] c y

private theorem wedge_reciprocal_transition {k : Type*} [CommRing k] [Algebra k A]
    [Module k M] (D : Derivation k A M) (a b t s : A)
    (hts : t * s = 1) (hb : b = a * t) :
    wedgeTwo (A := A) (D b) (D s) =
      (-s) • wedgeTwo (A := A) (D a) (D t) := by
  have hst : s * t = 1 := (mul_comm s t).trans hts
  have hs : D s = (-(s ^ 2)) • D t := D.leibniz_of_mul_eq_one hst
  have hc : (-(s ^ 2)) * t = -s := by
    rw [neg_mul, sq, mul_assoc, hst, mul_one]
  rw [hb, hs, wedge_smul_right, D.leibniz,
    wedge_add_left, wedge_smul_left, wedge_smul_left,
    wedgeTwo_self, smul_zero, zero_add, smul_smul, hc]

-- Compose the two existing pure-wedge formulas before specializing the chart rings.
private theorem exteriorBaseChange_map_ιMulti
    {B N : Type*} [CommRing B] [Algebra A B] [AddCommGroup N] [Module B N]
    (n : ℕ) (f : B ⊗[A] M →ₗ[B] N) (v : Fin n → M) :
    exteriorPower.map n f
        (KltDP.Compatibility.ExteriorPowerBaseChange.map A B n M
          (1 ⊗ₜ[A] exteriorPower.ιMulti A n v)) =
      exteriorPower.ιMulti B n (fun i => f (1 ⊗ₜ[A] v i)) :=
  (congrArg (exteriorPower.map n f)
    (KltDP.Compatibility.ExteriorPowerBaseChange.map_one_tmul_ιMulti A B n M v)).trans
      (exteriorPower.map_apply_ιMulti f (fun i => (1 : B) ⊗ₜ[A] v i))

end Wedge

variable {k : Type u} [Field k]

/-- The original second Rees chart. -/
abbrev rightChartRing (k : Type u) [Field k] :=
  chartRing (centerIdeal (k := k)) centerV

/-- The original homogeneous product localization, before any exceptional quotient. -/
abbrev overlapRing (k : Type u) [Field k] :=
  conormalOverlapRing (centerIdeal (k := k)) centerU centerV

/-- The original first chart restriction. -/
abbrev overlapLeft : reesChartRing k →+* overlapRing k :=
  conormalOverlapLeft (centerIdeal (k := k)) centerU centerV

/-- The original second chart restriction. -/
abbrev overlapRight : rightChartRing k →+* overlapRing k :=
  conormalOverlapRight (centerIdeal (k := k)) centerU centerV

/-- The original plane structure map of the overlap. -/
abbrev overlapBaseMap : planeRing k →+* overlapRing k :=
  conormalOverlapBaseMap (centerIdeal (k := k)) centerU centerV

local instance leftFieldAlgebra : Algebra k (reesChartRing k) :=
  FrobeniusBlowupDifferentialMap.chartFieldAlgebra

local instance rightFieldAlgebra : Algebra k (rightChartRing k) :=
  (chartConstants (centerV (k := k))).toAlgebra

local instance overlapPlaneAlgebra : Algebra (planeRing k) (overlapRing k) :=
  (overlapBaseMap (k := k)).toAlgebra

local instance overlapFieldAlgebra : Algebra k (overlapRing k) :=
  ((overlapBaseMap (k := k)).comp planeConstants).toAlgebra

local instance overlapLeftAlgebra : Algebra (reesChartRing k) (overlapRing k) :=
  (overlapLeft (k := k)).toAlgebra

local instance overlapRightAlgebra : Algebra (rightChartRing k) (overlapRing k) :=
  (overlapRight (k := k)).toAlgebra

local instance overlapPlaneTower :
    @IsScalarTower k (planeRing k) (overlapRing k)
      (inferInstance : SMul k (planeRing k))
      (overlapPlaneAlgebra (k := k)).toSMul
      (overlapFieldAlgebra (k := k)).toSMul :=
  @IsScalarTower.of_algebraMap_eq' k (planeRing k) (overlapRing k)
    _ _ _ (inferInstance : Algebra k (planeRing k))
    (overlapPlaneAlgebra (k := k)) (overlapFieldAlgebra (k := k)) rfl

local instance overlapLeftTower :
    @IsScalarTower k (reesChartRing k) (overlapRing k)
      (leftFieldAlgebra (k := k)).toSMul
      (overlapLeftAlgebra (k := k)).toSMul
      (overlapFieldAlgebra (k := k)).toSMul :=
  @IsScalarTower.of_algebraMap_eq k (reesChartRing k) (overlapRing k)
    _ _ _ (leftFieldAlgebra (k := k)) (overlapLeftAlgebra (k := k))
    (overlapFieldAlgebra (k := k)) fun r =>
      (conormalOverlapLeft_baseMap (centerIdeal (k := k)) centerU centerV
        (planeConstants r)).symm

local instance overlapRightTower :
    @IsScalarTower k (rightChartRing k) (overlapRing k)
      (rightFieldAlgebra (k := k)).toSMul
      (overlapRightAlgebra (k := k)).toSMul
      (overlapFieldAlgebra (k := k)).toSMul :=
  @IsScalarTower.of_algebraMap_eq k (rightChartRing k) (overlapRing k)
    _ _ _ (rightFieldAlgebra (k := k)) (overlapRightAlgebra (k := k))
    (overlapFieldAlgebra (k := k)) fun r =>
      (conormalOverlapRight_baseMap (centerIdeal (k := k)) centerU centerV
        (planeConstants r)).symm

theorem overlapPlaneAlgebra_algebraMap :
    algebraMap (planeRing k) (overlapRing k) = overlapBaseMap := rfl

/-- The native overlap Kähler module for the original field structure. -/
abbrev OverlapDifferential (k : Type u) [Field k] :=
  KaehlerDifferential k (overlapRing k)

/-- The native second-chart Kähler module for its original field structure. -/
abbrev RightDifferential (k : Type u) [Field k] :=
  KaehlerDifferential k (rightChartRing k)

/-- Localization of the original first chart differential module. Its
underlying map is exactly the pinned `mapBaseChange`. -/
def leftDifferentialEquiv :
    overlapRing k ⊗[reesChartRing k] ChartDifferential k ≃ₗ[overlapRing k]
      OverlapDifferential k := by
  letI : IsLocalization.Away (chartFraction (centerIdeal (k := k)) centerU centerV)
      (overlapRing k) := conormalOverlapLeft_isLocalization centerIdeal centerU centerV
  letI : Algebra.FormallyEtale (reesChartRing k) (overlapRing k) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (chartFraction (centerIdeal (k := k)) centerU centerV))
  exact KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
    k (reesChartRing k) (overlapRing k)

/-- Localization along the original second overlap projection. -/
def rightDifferentialEquiv :
    overlapRing k ⊗[rightChartRing k] RightDifferential k ≃ₗ[overlapRing k]
      OverlapDifferential k := by
  letI : IsLocalization.Away (chartFraction (centerIdeal (k := k)) centerV centerU)
      (overlapRing k) := conormalOverlapRight_isLocalization centerIdeal centerU centerV
  letI : Algebra.FormallyEtale (rightChartRing k) (overlapRing k) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (chartFraction (centerIdeal (k := k)) centerV centerU))
  exact KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
    k (rightChartRing k) (overlapRing k)

theorem leftDifferentialEquiv_one_tmul_D (x : reesChartRing k) :
    leftDifferentialEquiv (k := k) (1 ⊗ₜ[reesChartRing k] KaehlerDifferential.D k (reesChartRing k) x) =
      KaehlerDifferential.D k (overlapRing k) (overlapLeft x) := by
  change KaehlerDifferential.mapBaseChange k (reesChartRing k) (overlapRing k)
    (1 ⊗ₜ[reesChartRing k] KaehlerDifferential.D k (reesChartRing k) x) = _
  rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]
  rfl

theorem rightDifferentialEquiv_one_tmul_D (x : rightChartRing k) :
    rightDifferentialEquiv (k := k) (1 ⊗ₜ[rightChartRing k] KaehlerDifferential.D k (rightChartRing k) x) =
      KaehlerDifferential.D k (overlapRing k) (overlapRight x) := by
  change KaehlerDifferential.mapBaseChange k (rightChartRing k) (overlapRing k)
    (1 ⊗ₜ[rightChartRing k] KaehlerDifferential.D k (rightChartRing k) x) = _
  rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]
  rfl

/-- The two original plane coordinates on the overlap. -/
def overlapU : overlapRing k := overlapBaseMap uCoord
def overlapV : overlapRing k := overlapBaseMap vCoord

/-- The two actual reciprocal chart ratios. -/
def overlapT : overlapRing k := overlapLeft (chartW (k := k))
def overlapS : overlapRing k :=
  overlapRight (chartFraction (centerIdeal (k := k)) centerV centerU)

theorem overlapU_mul_overlapT :
    overlapU (k := k) * overlapT (k := k) = overlapV (k := k) := by
  have h := congrArg (overlapLeft (k := k)) (chartU_mul_chartW (k := k))
  simpa only [map_mul, chartU, baseMap, conormalOverlapLeft_baseMap] using h

theorem overlapV_mul_overlapS :
    overlapV (k := k) * overlapS (k := k) = overlapU (k := k) := by
  have h := congrArg (overlapRight (k := k))
    (chartBaseMap_mul_chartFraction (centerIdeal (k := k)) centerV centerU)
  simpa only [map_mul, conormalOverlapRight_baseMap] using h

theorem overlapT_mul_overlapS :
    overlapT (k := k) * overlapS (k := k) = 1 :=
  conormalOverlap_chartFractions_mul (centerIdeal (k := k)) centerU centerV

/-- The overlap ratio unit retains both original coordinate maps. -/
def overlapRatioUnit : (overlapRing k)ˣ where
  val := overlapT
  inv := overlapS
  val_inv := overlapT_mul_overlapS
  inv_val := (mul_comm _ _).trans overlapT_mul_overlapS

/-- The first original coordinate wedge, differentiated in the native overlap. -/
def leftForm : ⋀[overlapRing k]^2 (OverlapDifferential k) :=
  wedgeTwo (KaehlerDifferential.D k (overlapRing k) overlapU)
    (KaehlerDifferential.D k (overlapRing k) overlapT)

/-- The second original coordinate wedge, with order `(v,u/v)`. -/
def rightForm : ⋀[overlapRing k]^2 (OverlapDifferential k) :=
  wedgeTwo (KaehlerDifferential.D k (overlapRing k) overlapV)
    (KaehlerDifferential.D k (overlapRing k) overlapS)

/-- The original base coordinate two-form on the actual intersection. -/
def baseForm : ⋀[overlapRing k]^2 (OverlapDifferential k) :=
  wedgeTwo (KaehlerDifferential.D k (overlapRing k) overlapU)
    (KaehlerDifferential.D k (overlapRing k) overlapV)

theorem rightForm_eq :
    rightForm (k := k) = (-overlapS (k := k)) • leftForm (k := k) :=
  wedge_reciprocal_transition (KaehlerDifferential.D k (overlapRing k))
    overlapU overlapV overlapT overlapS overlapT_mul_overlapS overlapU_mul_overlapT.symm

theorem baseForm_left :
    baseForm (k := k) = overlapU (k := k) • leftForm (k := k) := by
  change wedgeTwo (KaehlerDifferential.D k (overlapRing k) overlapU)
      (KaehlerDifferential.D k (overlapRing k) overlapV) = _
  rw [← overlapU_mul_overlapT]
  exact wedgeTwo_derivation_mul (KaehlerDifferential.D k (overlapRing k)) overlapU overlapT

theorem baseForm_right :
    baseForm (k := k) = (-overlapV (k := k)) • rightForm (k := k) := by
  have hcoef : (-overlapV (k := k)) * (-overlapS (k := k)) = overlapU (k := k) :=
    (neg_mul_neg (overlapV (k := k)) (overlapS (k := k))).trans
      (overlapV_mul_overlapS (k := k))
  calc
    baseForm (k := k) = overlapU (k := k) • leftForm (k := k) :=
      baseForm_left (k := k)
    _ = ((-overlapV (k := k)) * (-overlapS (k := k))) • leftForm (k := k) :=
      congrArg (fun r : overlapRing k => r • leftForm (k := k)) hcoef.symm
    _ = (-overlapV (k := k)) • ((-overlapS (k := k)) • leftForm (k := k)) :=
      (smul_smul (-overlapV (k := k)) (-overlapS (k := k)) (leftForm (k := k))).symm
    _ = (-overlapV (k := k)) • rightForm (k := k) :=
      congrArg (fun ω : ⋀[overlapRing k]^2 (OverlapDifferential k) =>
        (-overlapV (k := k)) • ω) (rightForm_eq (k := k)).symm

/-- The top differential map from the original first chart, using
canonical scalar extension of its original exterior square. -/
def leftTopMap :
    overlapRing k ⊗[reesChartRing k] (⋀[reesChartRing k]^2 (ChartDifferential k)) →ₗ[overlapRing k]
      ⋀[overlapRing k]^2 (OverlapDifferential k) :=
  (exteriorPower.map 2 (leftDifferentialEquiv (k := k)).toLinearMap).comp
    (KltDP.Compatibility.ExteriorPowerBaseChange.map
      (reesChartRing k) (overlapRing k) 2 (ChartDifferential k))

/-- The corresponding original second chart map. -/
def rightTopMap :
    overlapRing k ⊗[rightChartRing k] (⋀[rightChartRing k]^2 (RightDifferential k)) →ₗ[overlapRing k]
      ⋀[overlapRing k]^2 (OverlapDifferential k) :=
  (exteriorPower.map 2 (rightDifferentialEquiv (k := k)).toLinearMap).comp
    (KltDP.Compatibility.ExteriorPowerBaseChange.map
      (rightChartRing k) (overlapRing k) 2 (RightDifferential k))

/-- The native second chart coordinate wedge, ordered `(v,u/v)`. -/
def rightChartForm : ⋀[rightChartRing k]^2 (RightDifferential k) :=
  wedgeTwo
    (KaehlerDifferential.D k (rightChartRing k) (chartBaseMap centerIdeal centerV vCoord))
    (KaehlerDifferential.D k (rightChartRing k) (chartFraction centerIdeal centerV centerU))

theorem leftTopMap_coordinate :
    leftTopMap (k := k) (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k)) = leftForm (k := k) := by
  change exteriorPower.map 2 (leftDifferentialEquiv (k := k)).toLinearMap
    (KltDP.Compatibility.ExteriorPowerBaseChange.map
      (reesChartRing k) (overlapRing k) 2 (ChartDifferential k)
      (1 ⊗ₜ[reesChartRing k] exteriorPower.ιMulti (reesChartRing k) 2
        ![KaehlerDifferential.D k (reesChartRing k) chartU,
          KaehlerDifferential.D k (reesChartRing k) chartW])) = _
  refine (exteriorBaseChange_map_ιMulti (A := reesChartRing k)
    (B := overlapRing k) (M := ChartDifferential k) (N := OverlapDifferential k) 2
    (leftDifferentialEquiv (k := k)).toLinearMap
    ![KaehlerDifferential.D k (reesChartRing k) chartU,
      KaehlerDifferential.D k (reesChartRing k) chartW]).trans ?_
  apply congrArg (exteriorPower.ιMulti (overlapRing k) 2)
  funext i
  fin_cases i
  · change leftDifferentialEquiv (k := k)
        (1 ⊗ₜ[reesChartRing k] KaehlerDifferential.D k (reesChartRing k) chartU) =
      KaehlerDifferential.D k (overlapRing k) overlapU
    simpa only [chartU, baseMap, conormalOverlapLeft_baseMap] using
      leftDifferentialEquiv_one_tmul_D (chartU (k := k))
  · exact leftDifferentialEquiv_one_tmul_D (chartW (k := k))

theorem rightTopMap_coordinate :
    rightTopMap (k := k) (1 ⊗ₜ[rightChartRing k] rightChartForm (k := k)) = rightForm (k := k) := by
  change exteriorPower.map 2 (rightDifferentialEquiv (k := k)).toLinearMap
    (KltDP.Compatibility.ExteriorPowerBaseChange.map
      (rightChartRing k) (overlapRing k) 2 (RightDifferential k)
      (1 ⊗ₜ[rightChartRing k] exteriorPower.ιMulti (rightChartRing k) 2
        ![KaehlerDifferential.D k (rightChartRing k) (chartBaseMap centerIdeal centerV vCoord),
          KaehlerDifferential.D k (rightChartRing k) (chartFraction centerIdeal centerV centerU)])) = _
  refine (exteriorBaseChange_map_ιMulti (A := rightChartRing k)
    (B := overlapRing k) (M := RightDifferential k) (N := OverlapDifferential k) 2
    (rightDifferentialEquiv (k := k)).toLinearMap
    ![KaehlerDifferential.D k (rightChartRing k)
        (chartBaseMap (centerIdeal (k := k)) centerV vCoord),
      KaehlerDifferential.D k (rightChartRing k)
        (chartFraction (centerIdeal (k := k)) centerV centerU)]).trans ?_
  apply congrArg (exteriorPower.ιMulti (overlapRing k) 2)
  funext i
  fin_cases i
  · change rightDifferentialEquiv (k := k)
        (1 ⊗ₜ[rightChartRing k] KaehlerDifferential.D k (rightChartRing k)
          (chartBaseMap centerIdeal centerV vCoord)) =
      KaehlerDifferential.D k (overlapRing k) overlapV
    simpa only [conormalOverlapRight_baseMap] using
      rightDifferentialEquiv_one_tmul_D
        (chartBaseMap (centerIdeal (k := k)) centerV vCoord)
  · exact rightDifferentialEquiv_one_tmul_D
      (chartFraction (centerIdeal (k := k)) centerV centerU)

/-- The actual base-to-overlap top differential map. Its source is the
scalar extension of the original plane's top line. -/
def baseTopMap :
    overlapRing k ⊗[planeRing k] (⋀[planeRing k]^2 (PlaneDifferential k)) →ₗ[overlapRing k]
      ⋀[overlapRing k]^2 (OverlapDifferential k) :=
  (exteriorPower.map 2
    (KaehlerDifferential.mapBaseChange k (planeRing k) (overlapRing k))).comp
      (KltDP.Compatibility.ExteriorPowerBaseChange.map
        (planeRing k) (overlapRing k) 2 (PlaneDifferential k))

theorem baseTopMap_coordinate :
    baseTopMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) = baseForm (k := k) := by
  change exteriorPower.map 2
    (KaehlerDifferential.mapBaseChange k (planeRing k) (overlapRing k))
    (KltDP.Compatibility.ExteriorPowerBaseChange.map
      (planeRing k) (overlapRing k) 2 (PlaneDifferential k)
      (1 ⊗ₜ[planeRing k] exteriorPower.ιMulti (planeRing k) 2
        ![KaehlerDifferential.D k (planeRing k) uCoord,
          KaehlerDifferential.D k (planeRing k) vCoord])) = _
  refine (exteriorBaseChange_map_ιMulti (A := planeRing k)
    (B := overlapRing k) (M := PlaneDifferential k) (N := OverlapDifferential k) 2
    (KaehlerDifferential.mapBaseChange k (planeRing k) (overlapRing k))
    ![KaehlerDifferential.D k (planeRing k) uCoord,
      KaehlerDifferential.D k (planeRing k) vCoord]).trans ?_
  apply congrArg (exteriorPower.ιMulti (overlapRing k) 2)
  funext i
  fin_cases i <;>
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ',
      KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul] <;>
    rfl

/-- Both coordinate descriptions are images under the original chart
differential maps, in the same actual native overlap module. -/
theorem baseTopMap_coordinate_left :
    baseTopMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) =
      overlapU (k := k) •
        leftTopMap (k := k) (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k)) := by
  exact (baseTopMap_coordinate (k := k)).trans
    ((baseForm_left (k := k)).trans
      (congrArg (fun ω : ⋀[overlapRing k]^2 (OverlapDifferential k) =>
        overlapU (k := k) • ω) (leftTopMap_coordinate (k := k)).symm))

theorem baseTopMap_coordinate_right :
    baseTopMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) =
      (-overlapV (k := k)) •
        rightTopMap (k := k) (1 ⊗ₜ[rightChartRing k] rightChartForm (k := k)) := by
  exact (baseTopMap_coordinate (k := k)).trans
    ((baseForm_right (k := k)).trans
      (congrArg (fun ω : ⋀[overlapRing k]^2 (OverlapDifferential k) =>
        (-overlapV (k := k)) • ω) (rightTopMap_coordinate (k := k)).symm))

end KltDP.Examples.FrobeniusBlowupDifferentialOverlap
