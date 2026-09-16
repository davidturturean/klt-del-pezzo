import KltDP.RingTheory.SmoothPrincipalDeterminantRestriction
import KltDP.Geometry.SmoothPrincipalAdjunctionChart

/-!
# Original ambient top forms and local adjunction respect ring restriction

The original Kähler map induces the original exterior map and its scalar
extension to the actual quotient ring. The canonical exterior base-change
comparison commutes with these maps on every pure wedge, hence on the
whole top exterior power. This transports determinant naturality to the
actual ambient top-form target of the local adjunction equivalence.
-/

noncomputable section

open scoped TensorProduct

universe u

namespace KltDP.RingTheory.SmoothPrincipalTopFormRestriction

open SmoothPrincipalDeterminantRestriction
open KltDP.Geometry

variable (R A A' : Type u) [CommRing R] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
  (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))

/-- The original ambient Kähler restriction induces the canonical top-form restriction. -/
def ambientExteriorMap :
    (⋀[A]^2 (KaehlerDifferential R A)) →ₗ[A] (⋀[A']^2 (KaehlerDifferential R A')) :=
  KltDP.LinearAlgebra.ExteriorPowerScalarMap.map A A' 2 (KaehlerDifferential.map R R A A')

/-- Extend the original top-form map by the original quotient coefficients. -/
def ambientTopTensorMap :
    (A ⧸ J) ⊗[A] (⋀[A]^2 (KaehlerDifferential R A)) →ₛₗ[quotientMap A A' J J' hφ]
      (A' ⧸ J') ⊗[A'] (⋀[A']^2 (KaehlerDifferential R A')) := by
  letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
  letI : Module (A ⧸ J) ((A' ⧸ J') ⊗[A'] (⋀[A']^2 (KaehlerDifferential R A'))) :=
    Module.compHom _ (quotientMap A A' J J' hφ)
  letI : IsScalarTower A (A ⧸ J) ((A' ⧸ J') ⊗[A'] (⋀[A']^2 (KaehlerDifferential R A'))) := by
    apply IsScalarTower.of_algebraMap_smul
    intro a m
    change quotientMap A A' J J' hφ (Ideal.Quotient.mk J a) • m = a • m
    rw [quotientMap, Ideal.quotientMap_mk]
    exact algebraMap_smul (A' ⧸ J') a m
  let g := (((TensorProduct.mk A' (A' ⧸ J') (⋀[A']^2 (KaehlerDifferential R A')) 1).restrictScalars A).comp
    (ambientExteriorMap R A A')).liftBaseChange (A ⧸ J)
  exact { toFun := g, map_add' := g.map_add, map_smul' := g.map_smul }

/-- Original coefficients and original wedges are retained by the actual tensor map. -/
theorem ambientTopTensorMap_wedge (s : A ⧸ J) (v : Fin 2 → KaehlerDifferential R A) :
    ambientTopTensorMap R A A' J J' hφ (s ⊗ₜ[A] exteriorPower.ιMulti A 2 v) =
      quotientMap A A' J J' hφ s ⊗ₜ[A']
        exteriorPower.ιMulti A' 2 (fun i => KaehlerDifferential.map R R A A' (v i)) := by
  change quotientMap A A' J J' hφ s • ((1 : A' ⧸ J') ⊗ₜ[A']
      KltDP.LinearAlgebra.ExteriorPowerScalarMap.map A A' 2
        (KaehlerDifferential.map R R A A') (exteriorPower.ιMulti A 2 v)) = _
  rw [KltDP.LinearAlgebra.ExteriorPowerScalarMap.map_ιMulti]
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
  [Algebra.IsStandardSmoothOfRelativeDimension 2 R A']

local instance sourceStandardSmooth : Algebra.IsStandardSmooth R A :=
  Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := R) (S := A) 2

local instance targetStandardSmooth : Algebra.IsStandardSmooth R A' :=
  Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := R) (S := A') 2

private theorem baseChange_square_wedge (s : A ⧸ J) (v : Fin 2 → KaehlerDifferential R A) :
    TopExteriorBaseChange.equiv (A' ⧸ J')
        (AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A')
        (ambientTopTensorMap R A A' J J' hφ (s ⊗ₜ[A] exteriorPower.ιMulti A 2 v)) =
      KltDP.LinearAlgebra.ExteriorPowerSemilinearMap.map (quotientMap A A' J J' hφ) 2
        (ambientTensorMap R A A' J J' hφ)
        (TopExteriorBaseChange.equiv (A ⧸ J)
          (AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A)
          (s ⊗ₜ[A] exteriorPower.ιMulti A 2 v)) := by
  rw [ambientTopTensorMap_wedge, TopExteriorBaseChange.equiv_tmul_ιMulti,
    TopExteriorBaseChange.equiv_tmul_ιMulti,
    (KltDP.LinearAlgebra.ExteriorPowerSemilinearMap.map (quotientMap A A' J J' hφ) 2
      (ambientTensorMap R A A' J J' hφ)).map_smulₛₗ,
    KltDP.LinearAlgebra.ExteriorPowerSemilinearMap.map_ιMulti]
  have hv : (fun i => ambientTensorMap R A A' J J' hφ
      ((1 : A ⧸ J) ⊗ₜ[A] v i)) =
      (fun i => (1 : A' ⧸ J') ⊗ₜ[A'] KaehlerDifferential.map R R A A' (v i)) := by
    funext i
    rw [ambientTensorMap_tmul, map_one]
  rw [hv]

/-- The original canonical exterior base-change comparison commutes with restriction. -/
theorem baseChange_square (x : (A ⧸ J) ⊗[A] (⋀[A]^2 (KaehlerDifferential R A))) :
    TopExteriorBaseChange.equiv (A' ⧸ J')
        (AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A')
        (ambientTopTensorMap R A A' J J' hφ x) =
      KltDP.LinearAlgebra.ExteriorPowerSemilinearMap.map (quotientMap A A' J J' hφ) 2
        (ambientTensorMap R A A' J J' hφ)
        (TopExteriorBaseChange.equiv (A ⧸ J)
          (AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero]
  | tmul s x =>
      let b := AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A
      obtain ⟨a, rfl⟩ := (AffineTopDifferentialFrame.determinantEquiv b).symm.surjective x
      simpa only [AffineTopDifferentialFrame.determinantEquiv_symm_apply,
        TensorProduct.tmul_smul] using baseChange_square_wedge R A A' J J' hφ (a • s) b
  | add x y hx hy => simp only [LinearMap.map_add, LinearEquiv.map_add, hx, hy]

variable [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A' ⧸ J')]
  (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)
  (hJ' : Ideal.span {(mappedEquation A A' J J' hφ d : A')} = J')
  (hd' : (mappedEquation A A' J J' hφ d : A') ∈ nonZeroDivisors A')

/-- The actual local adjunction map into the ambient top-form tensor commutes with restriction. -/
theorem moduleEquiv_restriction (n : KaehlerDifferential R (A ⧸ J)) :
    ambientTopTensorMap R A A' J J' hφ
        (SmoothPrincipalAdjunctionChart.moduleEquiv R A J d hJ hd n) =
      SmoothPrincipalAdjunctionChart.moduleEquiv R A' J'
        (mappedEquation A A' J J' hφ d) hJ' hd'
        (quotientDifferentialMap R A A' J J' hφ n) := by
  apply (TopExteriorBaseChange.equiv (A' ⧸ J')
    (AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A')).injective
  rw [baseChange_square]
  change KltDP.LinearAlgebra.ExteriorPowerSemilinearMap.map (quotientMap A A' J J' hφ) 2
      (ambientTensorMap R A A' J J' hφ)
      (TopExteriorBaseChange.equiv (A ⧸ J)
        (AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A)
        ((TopExteriorBaseChange.equiv (A ⧸ J)
          (AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A)).symm
          (SmoothPrincipalConormalDeterminant.determinantEquiv R A J d hJ hd n))) =
    TopExteriorBaseChange.equiv (A' ⧸ J')
      (AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A')
      ((TopExteriorBaseChange.equiv (A' ⧸ J')
        (AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A')).symm
        (SmoothPrincipalConormalDeterminant.determinantEquiv R A' J'
          (mappedEquation A A' J J' hφ d) hJ' hd'
          (quotientDifferentialMap R A A' J J' hφ n)))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact determinantEquiv_restriction R A A' J J' hφ d hJ hd hJ' hd' n

end KltDP.RingTheory.SmoothPrincipalTopFormRestriction
