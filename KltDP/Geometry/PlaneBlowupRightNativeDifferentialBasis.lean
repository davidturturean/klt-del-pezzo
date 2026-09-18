import KltDP.Geometry.PlaneBlowupNativeDifferentialBasis
import KltDP.Examples.FrobeniusBlowupDifferentialRightFrame

/-!
# The native coordinate basis on the original complementary plane Rees chart

The existing original right-chart polynomial isomorphism supplies the native
differential basis in the order exceptional parameter, homogeneous fraction.
No basis or determinant formula is assumed.
-/

noncomputable section

namespace KltDP.Geometry.PlaneBlowupRightNativeDifferentialBasis

open KltDP.Examples.FrobeniusBlowupContact
open KltDP.Examples.FrobeniusBlowupDifferentialOverlap
open KltDP.Examples.FrobeniusBlowupDifferentialOverlapFrame
open KltDP.Examples.FrobeniusBlowupDifferentialRightMap
open KltDP.Examples.FrobeniusBlowupDifferentialRightFrame

universe u

variable (k : Type u) [Field k]

local instance chartFieldAlgebra : Algebra k (rightChartRing k) :=
  KltDP.Examples.FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra

/-- Ordered polynomial coordinates on the original complementary chart. -/
def chartEquiv : MvPolynomial (Fin 2) k ≃ₐ[k] rightChartRing k :=
  (PlaneBlowupNativeDifferentialBasis.planeEquiv k).trans
    (rightChartPolynomialAlgEquiv (k := k)).symm

theorem chartEquiv_X_zero : chartEquiv k (MvPolynomial.X 0) = rightV (k := k) := by
  apply (rightChartPolynomialAlgEquiv (k := k)).injective
  rw [chartEquiv, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    PlaneBlowupNativeDifferentialBasis.planeEquiv_X_zero, rightChartPolynomialAlgEquiv_v]

theorem chartEquiv_X_one : chartEquiv k (MvPolynomial.X 1) = rightS (k := k) := by
  apply (rightChartPolynomialAlgEquiv (k := k)).injective
  rw [chartEquiv, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    PlaneBlowupNativeDifferentialBasis.planeEquiv_X_one, rightChartPolynomialAlgEquiv_s]

def basis : Basis (Fin 2) (rightChartRing k) (KaehlerDifferential k (rightChartRing k)) :=
  PolynomialCoordinateDifferentialBasis.basis k (rightChartRing k) 2 (chartEquiv k)

theorem basis_zero : basis k 0 = KaehlerDifferential.D k (rightChartRing k) (rightV (k := k)) := by
  rw [basis, PolynomialCoordinateDifferentialBasis.basis_apply, chartEquiv_X_zero]

theorem basis_one : basis k 1 = KaehlerDifferential.D k (rightChartRing k) (rightS (k := k)) := by
  rw [basis, PolynomialCoordinateDifferentialBasis.basis_apply, chartEquiv_X_one]

end KltDP.Geometry.PlaneBlowupRightNativeDifferentialBasis
