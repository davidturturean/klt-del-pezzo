import KltDP.Geometry.PolynomialCoordinateDifferentialBasis
import KltDP.Examples.FrobeniusBlowupDifferentialMap

/-!
# The native parameter/fraction differential basis on the actual plane blowup chart

This derives the two basis vectors on the already constructed original plane
Rees chart from its proved polynomial algebra isomorphism. It introduces no
new plane model or basis hypothesis. The order is exceptional parameter first,
actual homogeneous fraction second.
-/

noncomputable section

namespace KltDP.Geometry.PlaneBlowupNativeDifferentialBasis

open KltDP.Examples.FrobeniusBlowupContact
open KltDP.Examples.FrobeniusBlowupSmooth
open KltDP.Examples.FrobeniusBlowupDifferentialMap

universe u

variable (k : Type u) [Field k]

local instance chartFieldAlgebra : Algebra k (reesChartRing k) :=
  (chartConstants (centerU (k := k))).toAlgebra

/-- Ordered polynomial coordinates on the original polynomial plane. -/
def planeEquiv : MvPolynomial (Fin 2) k ≃ₐ[k] planeRing k :=
  ((MvPolynomial.finSuccEquiv k 1).trans
    (Polynomial.mapAlgEquiv ((MvPolynomial.finSuccEquiv k 0).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv k (Fin 0)))))).trans
    coordinateSwap

theorem planeEquiv_X_zero : planeEquiv k (MvPolynomial.X 0) = uCoord := by
  simp only [planeEquiv, AlgEquiv.trans_apply, MvPolynomial.finSuccEquiv_X_zero,
    Polynomial.coe_mapAlgEquiv, Polynomial.map_X]
  exact coordinateSwap_v

theorem planeEquiv_X_one : planeEquiv k (MvPolynomial.X 1) = vCoord := by
  have h : (MvPolynomial.finSuccEquiv k 1) (MvPolynomial.X (1 : Fin 2)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,
      MvPolynomial.finSuccEquiv_X_succ]
  simp only [planeEquiv, AlgEquiv.trans_apply, h, Polynomial.coe_mapAlgEquiv,
    Polynomial.map_C, MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]
  change coordinateSwap (Polynomial.C
    (((MvPolynomial.finSuccEquiv k 0).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv k (Fin 0))))
        (MvPolynomial.X (0 : Fin 1)))) = vCoord
  rw [AlgEquiv.trans_apply, MvPolynomial.finSuccEquiv_X_zero,
    Polynomial.coe_mapAlgEquiv, Polynomial.map_X]
  exact coordinateSwap_u (k := k)

/-- The actual Rees chart's ordered polynomial coordinate isomorphism. -/
def chartEquiv : MvPolynomial (Fin 2) k ≃ₐ[k] reesChartRing k :=
  (planeEquiv k).trans chartPolynomialAlgEquiv.symm

theorem chartEquiv_X_zero : chartEquiv k (MvPolynomial.X 0) = chartU := by
  apply chartPolynomialAlgEquiv.injective
  rw [chartEquiv, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    planeEquiv_X_zero, chartPolynomialAlgEquiv_u]

theorem chartEquiv_X_one : chartEquiv k (MvPolynomial.X 1) = chartW := by
  apply chartPolynomialAlgEquiv.injective
  rw [chartEquiv, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    planeEquiv_X_one, chartPolynomialAlgEquiv_w]

/-- The native differential basis is derived from those actual coordinates. -/
def basis : Basis (Fin 2) (reesChartRing k) (KaehlerDifferential k (reesChartRing k)) :=
  PolynomialCoordinateDifferentialBasis.basis k (reesChartRing k) 2 (chartEquiv k)

theorem basis_zero : basis k 0 = KaehlerDifferential.D k (reesChartRing k) chartU := by
  rw [basis, PolynomialCoordinateDifferentialBasis.basis_apply, chartEquiv_X_zero]

theorem basis_one : basis k 1 = KaehlerDifferential.D k (reesChartRing k) chartW := by
  rw [basis, PolynomialCoordinateDifferentialBasis.basis_apply, chartEquiv_X_one]

end KltDP.Geometry.PlaneBlowupNativeDifferentialBasis
