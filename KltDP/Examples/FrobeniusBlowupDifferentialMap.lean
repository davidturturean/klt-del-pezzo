import KltDP.Examples.FrobeniusBlowupDifferential
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The original scalar-extended differential map on the actual Rees chart

The source algebra is the original polynomial plane A and the target is
the original Rees chart B. Its existing A-algebra structure has algebraMap
exactly `baseMap`; it is never replaced by the coordinate isomorphism.
The field algebra uses the original scheme-structure map `chartConstants`.

Taking the exterior square of the existing map
`B ⊗[A] Ω[A/k] →ₗ[B] Ω[B/k]` sends the wedge of `1 ⊗ du`, `1 ⊗ dv`
to `chartU • (dchartU ∧ dchartW)`. The two actual coordinate derivations
give a functional taking the latter coordinate wedge to one. Thus the
actual differential image has the original nonzero exceptional coefficient.

This is a calculation of the actual scalar-extended differential map.
It does not assert global differential gluing, a canonical divisor, or
an intersection/degree formula.
-/

noncomputable section

open scoped TensorProduct

namespace KltDP.Examples.FrobeniusBlowupDifferentialMap

open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupDifferential
open KltDP.Geometry.AffineBlowup

universe u

variable {k : Type u} [Field k]

/-- Reuse the original base-plane algebra directly for instance synthesis. -/
local instance chartBaseAlgebra : Algebra (planeRing k) (reesChartRing k) :=
  chartAlgebra (centerIdeal (k := k)) (centerU (k := k))

/-- The field algebra is the original field-to-chart scheme structure map. -/
local instance chartFieldAlgebra : Algebra k (reesChartRing k) :=
  (chartConstants (centerU (k := k))).toAlgebra

theorem chartFieldAlgebra_algebraMap :
    algebraMap k (reesChartRing k) = chartConstants (centerU (k := k)) := rfl

/-- The original field and base-plane maps form their actual scalar tower. -/
local instance chartScalarTower :
    @IsScalarTower k (planeRing k) (reesChartRing k)
      (inferInstance : SMul k (planeRing k))
      (chartBaseAlgebra (k := k)).toSMul
      (chartFieldAlgebra (k := k)).toSMul :=
  @IsScalarTower.of_algebraMap_eq' k (planeRing k) (reesChartRing k)
    _ _ _ (inferInstance : Algebra k (planeRing k))
    (chartBaseAlgebra (k := k)) (chartFieldAlgebra (k := k)) rfl

/-- The A-algebra used below is exactly the existing Rees-chart algebra. -/
theorem chartBaseAlgebra_algebraMap :
    algebraMap (planeRing k) (reesChartRing k) = baseMap := rfl

/-- The coordinate isomorphism respects the original field maps. It does
not identify the base-plane map with an identity map. -/
def chartPolynomialAlgEquiv : reesChartRing k ≃ₐ[k] planeRing k where
  __ := chartPolynomialEquiv
  commutes' := uChartPolynomialEquiv_constants

theorem chartPolynomialAlgEquiv_u :
    chartPolynomialAlgEquiv (chartU (k := k)) = uCoord := chartPolynomialEquiv_u

theorem chartPolynomialAlgEquiv_w :
    chartPolynomialAlgEquiv (chartW (k := k)) = vCoord := chartPolynomialEquiv_w

/-- The actual Kähler module of the actual chart over its original field. -/
abbrev ChartDifferential (k : Type u) [Field k] :=
  KaehlerDifferential k (reesChartRing k)

/-- The actual scalar extension along the original, nonidentity base map. -/
abbrev ScalarExtendedPlaneDifferential (k : Type u) [Field k] :=
  reesChartRing k ⊗[planeRing k] PlaneDifferential k

/-- The existing Kähler scalar-extension map, with its original actions. -/
def chartDifferentialMap :
    ScalarExtendedPlaneDifferential k →ₗ[reesChartRing k] ChartDifferential k :=
  KaehlerDifferential.mapBaseChange k (planeRing k) (reesChartRing k)

/-- The universal differential map keeps the actual base-ring homomorphism. -/
theorem chartDifferentialMap_one_tmul_D (r : planeRing k) :
    chartDifferentialMap (1 ⊗ₜ[planeRing k]
        KaehlerDifferential.D k (planeRing k) r) =
      KaehlerDifferential.D k (reesChartRing k) (baseMap r) := by
  change KaehlerDifferential.mapBaseChange k (planeRing k) (reesChartRing k)
      (1 ⊗ₜ[planeRing k] KaehlerDifferential.D k (planeRing k) r) =
    KaehlerDifferential.D k (reesChartRing k)
      (algebraMap (planeRing k) (reesChartRing k) r)
  rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]

/-- The original exterior-square functor applied to the actual differential map. -/
def chartTopDifferentialMap :
    (⋀[reesChartRing k]^2 (ScalarExtendedPlaneDifferential k)) →ₗ[reesChartRing k]
      (⋀[reesChartRing k]^2 (ChartDifferential k)) :=
  exteriorPower.map 2 (chartDifferentialMap (k := k))

/-- The two source coordinate differentials after actual scalar extension. -/
def scalarExtendedCoordinateTopForm :
    ⋀[reesChartRing k]^2 (ScalarExtendedPlaneDifferential k) :=
  wedgeTwo (A := reesChartRing k)
    (1 ⊗ₜ[planeRing k] KaehlerDifferential.D k (planeRing k) uCoord)
    (1 ⊗ₜ[planeRing k] KaehlerDifferential.D k (planeRing k) vCoord)

/-- The coordinate wedge in the actual chart's Kähler module. -/
def chartCoordinateTopForm : ⋀[reesChartRing k]^2 (ChartDifferential k) :=
  wedgeTwo (A := reesChartRing k)
    (KaehlerDifferential.D k (reesChartRing k) chartU)
    (KaehlerDifferential.D k (reesChartRing k) chartW)

set_option maxHeartbeats 800000 in
/-- The coefficient of the actual differential map is the actual chart equation. -/
theorem chartTopDifferentialMap_coordinate :
    chartTopDifferentialMap (k := k) (scalarExtendedCoordinateTopForm (k := k)) =
      chartU (k := k) • chartCoordinateTopForm (k := k) := by
  change exteriorPower.map 2 (chartDifferentialMap (k := k))
      (exteriorPower.ιMulti (reesChartRing k) 2
        ![1 ⊗ₜ[planeRing k] KaehlerDifferential.D k (planeRing k) uCoord,
          1 ⊗ₜ[planeRing k] KaehlerDifferential.D k (planeRing k) vCoord]) = _
  rw [exteriorPower.map_apply_ιMulti]
  have hvec :
      (chartDifferentialMap (k := k)) ∘
          ![1 ⊗ₜ[planeRing k] KaehlerDifferential.D k (planeRing k) uCoord,
            1 ⊗ₜ[planeRing k] KaehlerDifferential.D k (planeRing k) vCoord] =
        ![KaehlerDifferential.D k (reesChartRing k) (baseMap uCoord),
          KaehlerDifferential.D k (reesChartRing k) (baseMap vCoord)] := by
    funext i
    fin_cases i <;> exact chartDifferentialMap_one_tmul_D _
  refine (congrArg
    (fun v : Fin 2 → ChartDifferential k =>
      exteriorPower.ιMulti (reesChartRing k) 2 v) hvec).trans ?_
  change wedgeTwo (A := reesChartRing k)
      (KaehlerDifferential.D k (reesChartRing k) chartU)
      (KaehlerDifferential.D k (reesChartRing k) (baseMap vCoord)) = _
  rw [← chartU_mul_chartW]
  exact wedgeTwo_derivation_mul
    (k := k) (A := reesChartRing k) (M := ChartDifferential k)
    (KaehlerDifferential.D k (reesChartRing k)) chartU chartW

private theorem coordinateDerivation_kernel (d : Derivation k (planeRing k) (planeRing k))
    (x : planeRing k) (hx : (chartPolynomialAlgEquiv (k := k)).symm x = 0) :
    (chartPolynomialAlgEquiv (k := k)).symm (d x) = 0 := by
  have hx0 : x = 0 := (chartPolynomialAlgEquiv (k := k)).symm.injective
    (hx.trans (map_zero (chartPolynomialAlgEquiv (k := k)).symm).symm)
  simp only [hx0, map_zero]

/-- Transport only the coordinate derivation through the original k-algebra
isomorphism; this construction does not change the A-algebra structure on B. -/
def coordinateDerivation (d : Derivation k (planeRing k) (planeRing k)) :
    Derivation k (reesChartRing k) (reesChartRing k) :=
  Derivation.liftOfRightInverse
    (f := (chartPolynomialAlgEquiv (k := k)).symm.toAlgHom)
    (f_inv := chartPolynomialAlgEquiv (k := k))
    (chartPolynomialAlgEquiv (k := k)).symm_apply_apply
    (d := d) (coordinateDerivation_kernel d)

theorem coordinateDerivation_apply (d : Derivation k (planeRing k) (planeRing k))
    (x : reesChartRing k) :
    coordinateDerivation d x =
      (chartPolynomialAlgEquiv (k := k)).symm (d (chartPolynomialAlgEquiv x)) := rfl

@[simp] theorem coordinateDerivation_partialU_u :
    coordinateDerivation partialU (chartU (k := k)) = 1 := by
  rw [coordinateDerivation_apply, chartPolynomialAlgEquiv_u, partialU_u, map_one]

@[simp] theorem coordinateDerivation_partialU_w :
    coordinateDerivation partialU (chartW (k := k)) = 0 := by
  rw [coordinateDerivation_apply, chartPolynomialAlgEquiv_w, partialU_v, map_zero]

@[simp] theorem coordinateDerivation_partialV_u :
    coordinateDerivation partialV (chartU (k := k)) = 0 := by
  rw [coordinateDerivation_apply, chartPolynomialAlgEquiv_u, partialV_u, map_zero]

@[simp] theorem coordinateDerivation_partialV_w :
    coordinateDerivation partialV (chartW (k := k)) = 1 := by
  rw [coordinateDerivation_apply, chartPolynomialAlgEquiv_w, partialV_v, map_one]

/-- The two actual chart derivations give the original determinant pairing. -/
def chartTopFormEvaluator :
    (⋀[reesChartRing k]^2 (ChartDifferential k)) →ₗ[reesChartRing k] reesChartRing k :=
  exteriorPower.alternatingMapToDual (reesChartRing k) (ChartDifferential k) 2
    ![(coordinateDerivation partialU).liftKaehlerDifferential,
      (coordinateDerivation partialV).liftKaehlerDifferential]

theorem chartTopFormEvaluator_coordinateTopForm :
    chartTopFormEvaluator (k := k) (chartCoordinateTopForm (k := k)) = 1 := by
  simp [chartTopFormEvaluator, chartCoordinateTopForm, wedgeTwo,
    exteriorPower.alternatingMapToDual_apply_ιMulti, Matrix.det_fin_two]

/-- This is the coordinate functional of the actual exterior differential map. -/
def chartJacobianCoordinateMap :
    (⋀[reesChartRing k]^2 (ScalarExtendedPlaneDifferential k)) →ₗ[reesChartRing k]
      reesChartRing k :=
  (chartTopFormEvaluator (k := k)).comp (chartTopDifferentialMap (k := k))

theorem chartJacobianCoordinateMap_coordinate :
    chartJacobianCoordinateMap (k := k) (scalarExtendedCoordinateTopForm (k := k)) = chartU := by
  change chartTopFormEvaluator (k := k)
      (chartTopDifferentialMap (k := k) (scalarExtendedCoordinateTopForm (k := k))) = _
  rw [chartTopDifferentialMap_coordinate, map_smul,
    chartTopFormEvaluator_coordinateTopForm, smul_eq_mul, mul_one]

/-- The nonzero coefficient is the original polynomial exceptional coordinate
under the original chart presentation. -/
theorem chartJacobianCoordinateMap_polynomial_coordinate :
    chartPolynomialEquiv (k := k)
        (chartJacobianCoordinateMap (k := k) (scalarExtendedCoordinateTopForm (k := k))) = uCoord := by
  rw [chartJacobianCoordinateMap_coordinate, chartPolynomialEquiv_u]

theorem chartTopDifferentialMap_coordinate_ne_zero :
    chartTopDifferentialMap (k := k) (scalarExtendedCoordinateTopForm (k := k)) ≠ 0 := by
  intro h
  have hu : chartU (k := k) = 0 := by
    have he := chartJacobianCoordinateMap_coordinate (k := k)
    change chartTopFormEvaluator (k := k)
        (chartTopDifferentialMap (k := k) (scalarExtendedCoordinateTopForm (k := k))) = chartU at he
    rw [h, map_zero] at he
    exact he.symm
  have hp := congrArg (chartPolynomialEquiv (k := k)) hu
  rw [chartPolynomialEquiv_u, map_zero] at hp
  exact uCoord_ne_zero hp

end KltDP.Examples.FrobeniusBlowupDifferentialMap
