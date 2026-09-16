import KltDP.Examples.FrobeniusBlowupDifferentialRightMap
import KltDP.Examples.FrobeniusExceptionalCharts

/-!
# The original complementary-chart wedge is a native frame

Transport the original polynomial coordinate derivations through the already
proved second-chart polynomial presentation. Their determinant evaluates the
existing native wedge `rightChartForm` to one. Original standard smoothness
supplies rank one for the exterior square, so this exact evaluator is an
equivalence whose inverse multiplies by that original native wedge.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Examples.FrobeniusBlowupDifferentialRightFrame

open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupDifferential
open FrobeniusBlowupDifferentialOverlap FrobeniusBlowupDifferentialOverlapFrame
open FrobeniusBlowupDifferentialRightMap FrobeniusExceptionalCharts
open KltDP.Geometry KltDP.Geometry.AffineBlowup

universe u

private theorem frameInverseIdentities {A M : Type u}
    [CommRing A] [AddCommGroup M] [Module A M]
    (e : M ≃ₗ[A] A) (F : M →ₗ[A] A) (w : M) (hw : F w = 1) :
    F.comp (LinearMap.toSpanSingleton A M w) = LinearMap.id ∧
      (LinearMap.toSpanSingleton A M w).comp F = LinearMap.id := by
  have hswap (x y : M) : e x • y = e y • x := by
    apply e.injective
    simp only [LinearEquiv.map_smul, smul_eq_mul]
    exact mul_comm _ _
  constructor
  · apply LinearMap.ext
    intro a
    change F (a • w) = a
    rw [LinearMap.map_smul, hw, smul_eq_mul, mul_one]
  · apply LinearMap.ext
    intro x
    change F x • w = x
    apply e.injective
    rw [LinearEquiv.map_smul, smul_eq_mul]
    calc
      F x * e w = e w * F x := mul_comm _ _
      _ = e x := by
        have hx := congrArg F (hswap w x)
        simpa only [LinearMap.map_smul, hw, smul_eq_mul, mul_one] using hx

variable {k : Type u} [Field k]

local instance : Algebra (planeRing k) (rightChartRing k) :=
  FrobeniusBlowupDifferentialRightMap.rightBaseAlgebra
local instance : Algebra k (rightChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra

theorem rightChartPolynomialAlgEquiv_v :
    rightChartPolynomialAlgEquiv (k := k) (rightV (k := k)) = uCoord :=
  vChart_selected_equation (k := k)

theorem rightChartPolynomialAlgEquiv_s :
    rightChartPolynomialAlgEquiv (k := k) (rightS (k := k)) = vCoord :=
  vChartPolynomialEquiv_coordinate (k := k)

private theorem rightCoordinateDerivation_kernel
    (d : Derivation k (planeRing k) (planeRing k))
    (x : planeRing k) (hx : (rightChartPolynomialAlgEquiv (k := k)).symm x = 0) :
    (rightChartPolynomialAlgEquiv (k := k)).symm (d x) = 0 := by
  have hx0 : x = 0 := (rightChartPolynomialAlgEquiv (k := k)).symm.injective
    (hx.trans (map_zero (rightChartPolynomialAlgEquiv (k := k)).symm).symm)
  simp only [hx0, map_zero]

/-- Transport only the derivation, retaining both original chart algebras. -/
def rightCoordinateDerivation (d : Derivation k (planeRing k) (planeRing k)) :
    Derivation k (rightChartRing k) (rightChartRing k) :=
  Derivation.liftOfRightInverse
    (f := (rightChartPolynomialAlgEquiv (k := k)).symm.toAlgHom)
    (f_inv := rightChartPolynomialAlgEquiv (k := k))
    (rightChartPolynomialAlgEquiv (k := k)).symm_apply_apply
    (d := d) (rightCoordinateDerivation_kernel d)

theorem rightCoordinateDerivation_apply (d : Derivation k (planeRing k) (planeRing k))
    (x : rightChartRing k) :
    rightCoordinateDerivation d x =
      (rightChartPolynomialAlgEquiv (k := k)).symm (d (rightChartPolynomialAlgEquiv x)) := rfl

@[simp] theorem rightCoordinateDerivation_partialU_v :
    rightCoordinateDerivation partialU (rightV (k := k)) = 1 := by
  rw [rightCoordinateDerivation_apply, rightChartPolynomialAlgEquiv_v, partialU_u, map_one]

@[simp] theorem rightCoordinateDerivation_partialU_s :
    rightCoordinateDerivation partialU (rightS (k := k)) = 0 := by
  rw [rightCoordinateDerivation_apply, rightChartPolynomialAlgEquiv_s, partialU_v, map_zero]

@[simp] theorem rightCoordinateDerivation_partialV_v :
    rightCoordinateDerivation partialV (rightV (k := k)) = 0 := by
  rw [rightCoordinateDerivation_apply, rightChartPolynomialAlgEquiv_v, partialV_u, map_zero]

@[simp] theorem rightCoordinateDerivation_partialV_s :
    rightCoordinateDerivation partialV (rightS (k := k)) = 1 := by
  rw [rightCoordinateDerivation_apply, rightChartPolynomialAlgEquiv_s, partialV_v, map_one]

/-- The actual complementary-chart determinant functional. -/
def rightTopFormEvaluator :
    (⋀[rightChartRing k]^2 (RightDifferential k)) →ₗ[rightChartRing k] rightChartRing k :=
  exteriorPower.alternatingMapToDual (rightChartRing k) (RightDifferential k) 2
    ![(rightCoordinateDerivation partialU).liftKaehlerDifferential,
      (rightCoordinateDerivation partialV).liftKaehlerDifferential]

theorem rightTopFormEvaluator_coordinate :
    rightTopFormEvaluator (k := k) (rightChartForm (k := k)) = 1 := by
  change rightTopFormEvaluator (k := k)
    (wedgeTwo (KaehlerDifferential.D k (rightChartRing k) (rightV (k := k)))
      (KaehlerDifferential.D k (rightChartRing k) (rightS (k := k)))) = 1
  simp [rightTopFormEvaluator, wedgeTwo,
    exteriorPower.alternatingMapToDual_apply_ιMulti, Matrix.det_fin_two]

/-- The exact native determinant evaluator is a frame isomorphism, with
inverse the original native wedge. Rank comes from original standard smoothness. -/
def rightTopDifferentialEquiv :
    (⋀[rightChartRing k]^2 (RightDifferential k)) ≃ₗ[rightChartRing k] rightChartRing k := by
  letI := rightChart_standardSmooth (k := k)
  let e : (⋀[rightChartRing k]^2 (RightDifferential k)) ≃ₗ[rightChartRing k] rightChartRing k :=
    AffineTopDifferentialFrame.standardSmoothTopDifferentialEquiv k (rightChartRing k)
  let F : (⋀[rightChartRing k]^2 (RightDifferential k)) →ₗ[rightChartRing k] rightChartRing k :=
    rightTopFormEvaluator (k := k)
  let w : ⋀[rightChartRing k]^2 (RightDifferential k) := rightChartForm (k := k)
  let G : rightChartRing k →ₗ[rightChartRing k] (⋀[rightChartRing k]^2 (RightDifferential k)) :=
    LinearMap.toSpanSingleton (rightChartRing k) (⋀[rightChartRing k]^2 (RightDifferential k)) w
  have h := frameInverseIdentities (A := rightChartRing k)
    (M := ⋀[rightChartRing k]^2 (RightDifferential k)) e F w
    (rightTopFormEvaluator_coordinate (k := k))
  exact LinearEquiv.ofLinear F G h.1 h.2

theorem rightTopDifferentialEquiv_apply
    (ω : ⋀[rightChartRing k]^2 (RightDifferential k)) :
    rightTopDifferentialEquiv (k := k) ω = rightTopFormEvaluator (k := k) ω := rfl

theorem rightTopDifferentialEquiv_symm_apply (r : rightChartRing k) :
    (rightTopDifferentialEquiv (k := k)).symm r = r • rightChartForm (k := k) := rfl

theorem rightChartForm_expansion (ω : ⋀[rightChartRing k]^2 (RightDifferential k)) :
    rightTopFormEvaluator (k := k) ω • rightChartForm (k := k) = ω :=
  (rightTopDifferentialEquiv (k := k)).symm_apply_apply ω

/-- The actual whole second-chart differential has its proved coefficient
in the original native frame. -/
theorem rightTopDifferentialEquiv_differential (ω : planeRightModule k) :
    rightTopDifferentialEquiv (k := k) (planeRightTopMap (k := k) ω) =
      planeRightFrameEquiv (k := k) ω * (-rightV (k := k)) := by
  rw [planeRightTopMap_frame, LinearEquiv.map_smul, rightTopDifferentialEquiv_apply,
    rightTopFormEvaluator_coordinate, smul_eq_mul, mul_one]

/-- The same exact frame gives an isomorphism of the original native tilde sheaf. -/
def rightTopDifferentialSheafIso :
    (FrobeniusBlowupDifferentialPullback.rightNativeModule k).tilde ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of (rightChartRing k))).ringCatSheaf :=
  AffineModuleTilde.linearEquivIso
    (M := FrobeniusBlowupDifferentialPullback.rightNativeModule k)
    (N := ModuleCat.of (rightChartRing k) (rightChartRing k))
    (rightTopDifferentialEquiv (k := k)) ≪≫ AffineModuleTilde.unitIso (rightChartRing k)

end KltDP.Examples.FrobeniusBlowupDifferentialRightFrame
