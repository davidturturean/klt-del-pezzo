import KltDP.Examples.FrobeniusBlowupDifferentialPullbackComp
import KltDP.Examples.FrobeniusCoordinateDifferentialFrame

/-!
# The actual determinant map on the complementary Rees chart

Construct the top-differential map along the original plane-to-second-chart
ring map. Its value on the original plane wedge is minus the original
exceptional equation times the existing native wedge ordered `(v,u/v)`.
The original source frame then determines this actual map on its whole module.
No determinant compatibility or canonical divisor formula is a premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace KltDP.Examples.FrobeniusBlowupDifferentialRightMap

open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupDifferential
open FrobeniusBlowupDifferentialOverlap FrobeniusCoordinateDifferentialFrame
open KltDP.Geometry KltDP.Geometry.AffineBlowup

universe u

private theorem wedgeTwo_swap {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (x y : M) : wedgeTwo (A := A) x y = -wedgeTwo (A := A) y x := by
  have hv : ![x, y] = ![y, x] ∘ Equiv.swap (0 : Fin 2) 1 := by
    funext i
    fin_cases i <;> rfl
  exact (congrArg (exteriorPower.ιMulti A 2) hv).trans
    ((exteriorPower.ιMulti A 2).map_swap ![y, x] (by decide : (0 : Fin 2) ≠ 1))

private theorem exteriorBaseChange_map_ιMulti
    {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (n : ℕ) (f : B ⊗[A] M →ₗ[B] N) (v : Fin n → M) :
    exteriorPower.map n f
        (KltDP.Compatibility.ExteriorPowerBaseChange.map A B n M
          (1 ⊗ₜ[A] exteriorPower.ιMulti A n v)) =
      exteriorPower.ιMulti B n (fun i => f (1 ⊗ₜ[A] v i)) :=
  (congrArg (exteriorPower.map n f)
    (KltDP.Compatibility.ExteriorPowerBaseChange.map_one_tmul_ιMulti A B n M v)).trans
      (exteriorPower.map_apply_ιMulti f (fun i => (1 : B) ⊗ₜ[A] v i))

variable {k : Type u} [Field k]

/-- Preserve the original Rees-chart algebra over the original plane. -/
local instance rightBaseAlgebra : Algebra (planeRing k) (rightChartRing k) :=
  chartAlgebra (centerIdeal (k := k)) (centerV (k := k))
local instance : Algebra k (rightChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra
local instance rightScalarTower :
    @IsScalarTower k (planeRing k) (rightChartRing k)
      (inferInstance : SMul k (planeRing k)) (rightBaseAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra (k := k)).toSMul :=
  @IsScalarTower.of_algebraMap_eq' k (planeRing k) (rightChartRing k)
    _ _ _ (inferInstance : Algebra k (planeRing k)) (rightBaseAlgebra (k := k))
    (FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra (k := k)) rfl

abbrev rightBaseMap : planeRing k →+* rightChartRing k :=
  chartBaseMap (centerIdeal (k := k)) (centerV (k := k))

/-- The original exceptional equation and reciprocal chart coordinate. -/
abbrev rightV : rightChartRing k := rightBaseMap (k := k) vCoord
abbrev rightS : rightChartRing k :=
  chartFraction (centerIdeal (k := k)) (centerV (k := k)) (centerU (k := k))

theorem rightV_mul_rightS :
    rightV (k := k) * rightS (k := k) = rightBaseMap (k := k) uCoord :=
  chartBaseMap_mul_chartFraction (centerIdeal (k := k)) (centerV (k := k))
    (centerU (k := k))

/-- The original Kähler base-change map, with its actual scalar actions. -/
def rightDifferentialMap :
    rightChartRing k ⊗[planeRing k] PlaneDifferential k →ₗ[rightChartRing k]
      RightDifferential k :=
  KaehlerDifferential.mapBaseChange k (planeRing k) (rightChartRing k)

theorem rightDifferentialMap_one_tmul_D (r : planeRing k) :
    rightDifferentialMap (k := k)
        (1 ⊗ₜ[planeRing k] KaehlerDifferential.D k (planeRing k) r) =
      KaehlerDifferential.D k (rightChartRing k) (rightBaseMap r) := by
  change KaehlerDifferential.mapBaseChange k (planeRing k) (rightChartRing k)
      (1 ⊗ₜ[planeRing k] KaehlerDifferential.D k (planeRing k) r) =
    KaehlerDifferential.D k (rightChartRing k)
      (algebraMap (planeRing k) (rightChartRing k) r)
  rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]

abbrev planeRightModule (k : Type u) [Field k] : ModuleCat (rightChartRing k) :=
  ModuleCat.of (rightChartRing k)
    (rightChartRing k ⊗[planeRing k] (⋀[planeRing k]^2 (PlaneDifferential k)))

/-- The original exterior differential preceded by the canonical exterior
scalar-extension comparison, directly on the original second Rees chart. -/
def planeRightTopMap : planeRightModule k →ₗ[rightChartRing k]
    ⋀[rightChartRing k]^2 (RightDifferential k) :=
  (exteriorPower.map 2 (rightDifferentialMap (k := k))).comp
    (KltDP.Compatibility.ExteriorPowerBaseChange.map
      (planeRing k) (rightChartRing k) 2 (PlaneDifferential k))

/-- The sign comes from the existing native order `(v,u/v)`; the defining
equation is the original image of `v`, before any exceptional quotient. -/
theorem planeRightTopMap_coordinate :
    planeRightTopMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) =
      (-rightV (k := k)) • rightChartForm (k := k) := by
  refine (exteriorBaseChange_map_ιMulti 2 (rightDifferentialMap (k := k))
    ![KaehlerDifferential.D k (planeRing k) uCoord,
      KaehlerDifferential.D k (planeRing k) vCoord]).trans ?_
  have hv :
      (fun i : Fin 2 => rightDifferentialMap (k := k)
        (1 ⊗ₜ[planeRing k] (![KaehlerDifferential.D k (planeRing k) uCoord,
          KaehlerDifferential.D k (planeRing k) vCoord] i))) =
      ![KaehlerDifferential.D k (rightChartRing k) (rightBaseMap uCoord),
        KaehlerDifferential.D k (rightChartRing k) (rightV (k := k))] := by
    funext i
    fin_cases i <;> exact rightDifferentialMap_one_tmul_D _
  refine (congrArg (exteriorPower.ιMulti (rightChartRing k) 2) hv).trans ?_
  change wedgeTwo (A := rightChartRing k)
    (KaehlerDifferential.D k (rightChartRing k) (rightBaseMap uCoord))
    (KaehlerDifferential.D k (rightChartRing k) (rightV (k := k))) = _
  refine (congrArg (fun r : rightChartRing k =>
    wedgeTwo (A := rightChartRing k)
      (KaehlerDifferential.D k (rightChartRing k) r)
      (KaehlerDifferential.D k (rightChartRing k) (rightV (k := k))))
    (rightV_mul_rightS (k := k)).symm).trans ?_
  refine (wedgeTwo_swap (A := rightChartRing k) (M := RightDifferential k)
    (KaehlerDifferential.D k (rightChartRing k) (rightV (k := k) * rightS (k := k)))
    (KaehlerDifferential.D k (rightChartRing k) (rightV (k := k)))).trans ?_
  exact (congrArg Neg.neg
    (wedgeTwo_derivation_mul (KaehlerDifferential.D k (rightChartRing k))
      (rightV (k := k)) (rightS (k := k)))).trans
    (neg_smul (rightV (k := k)) (rightChartForm (k := k))).symm

/-- Extend the already proved original plane frame along this actual map. -/
def planeRightFrameEquiv : planeRightModule k ≃ₗ[rightChartRing k] rightChartRing k :=
  (LinearEquiv.baseChange (planeRing k) (rightChartRing k)
    (⋀[planeRing k]^2 (PlaneDifferential k)) (planeRing k)
      (coordinateTopDifferentialEquiv (k := k))).trans
    (TensorProduct.AlgebraTensorModule.rid
      (planeRing k) (rightChartRing k) (rightChartRing k))

theorem planeRightFrameEquiv_coordinate :
    planeRightFrameEquiv (k := k)
      (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) = 1 := by
  change algebraMap (planeRing k) (rightChartRing k)
    (coordinateTopDifferentialEquiv (k := k) (coordinateTopForm (k := k))) * 1 = 1
  rw [coordinateTopDifferentialEquiv_apply,
    coordinateTopFormEvaluator_coordinateTopForm, map_one, mul_one]

theorem planeRightFrame_expansion (ω : planeRightModule k) :
    planeRightFrameEquiv (k := k) ω •
      (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) = ω := by
  apply (planeRightFrameEquiv (k := k)).injective
  rw [LinearEquiv.map_smul, planeRightFrameEquiv_coordinate, smul_eq_mul, mul_one]

/-- The entire actual second-chart map has the original exceptional
equation as its coefficient, with the native coordinate-order sign. -/
theorem planeRightTopMap_frame (ω : planeRightModule k) :
    planeRightTopMap (k := k) ω =
      (planeRightFrameEquiv (k := k) ω * (-rightV (k := k))) • rightChartForm (k := k) := by
  calc
    _ = planeRightTopMap (k := k)
        (planeRightFrameEquiv (k := k) ω •
          (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))) :=
      congrArg (planeRightTopMap (k := k)) (planeRightFrame_expansion ω).symm
    _ = planeRightFrameEquiv (k := k) ω •
        planeRightTopMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) :=
      LinearMap.map_smul (planeRightTopMap (k := k))
        (planeRightFrameEquiv (k := k) ω)
        (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))
    _ = planeRightFrameEquiv (k := k) ω •
        ((-rightV (k := k)) • rightChartForm (k := k)) :=
      congrArg (fun η : ⋀[rightChartRing k]^2 (RightDifferential k) =>
        planeRightFrameEquiv (k := k) ω • η) (planeRightTopMap_coordinate (k := k))
    _ = _ := smul_smul (planeRightFrameEquiv (k := k) ω)
      (-rightV (k := k)) (rightChartForm (k := k))

end KltDP.Examples.FrobeniusBlowupDifferentialRightMap
