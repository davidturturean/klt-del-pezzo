import KltDP.Geometry.PlaneBlowupNativeDifferentialBasis
import KltDP.Geometry.EtaleCoordinateDifferentialBasis

/-!
# The original smooth-point coordinate source has its actual native basis

Compose the original plane coordinate map with the proved ordered polynomial
plane isomorphism. Its standard-smooth dimension-zero presentation supplies
the actual differential basis. The vectors are precisely `d(φ u)` and `d(φ v)`.
-/

noncomputable section

namespace KltDP.Geometry.SmoothPointBlowupSourceBasis

open KltDP.Examples.FrobeniusBlowupContact
open PlaneBlowupNativeDifferentialBasis

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

/-- The source basis is derived from the original plane coordinates. -/
def basis : Basis (Fin 2) S (KaehlerDifferential k S) := by
  let g := φ.comp (planeEquiv k).toAlgHom
  letI : Algebra (MvPolynomial (Fin 2) k) S := g.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial (Fin 2) k) S :=
    IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin 2) k) S :=
    hφ.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv (planeEquiv k).toRingEquiv)
  exact EtaleCoordinateDifferentialBasis.basis k S 2

/-- Each basis vector is the differential of the literal original coordinate image. -/
theorem basis_apply (i : Fin 2) :
    basis k φ hφ i = KaehlerDifferential.D k S (φ (planeEquiv k (MvPolynomial.X i))) := by
  let g := φ.comp (planeEquiv k).toAlgHom
  letI : Algebra (MvPolynomial (Fin 2) k) S := g.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial (Fin 2) k) S :=
    IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin 2) k) S :=
    hφ.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv (planeEquiv k).toRingEquiv)
  exact EtaleCoordinateDifferentialBasis.basis_apply k S 2 i

theorem basis_zero : basis k φ hφ 0 = KaehlerDifferential.D k S (φ uCoord) := by
  rw [basis_apply, planeEquiv_X_zero]

theorem basis_one : basis k φ hφ 1 = KaehlerDifferential.D k S (φ vCoord) := by
  rw [basis_apply, planeEquiv_X_one]

end KltDP.Geometry.SmoothPointBlowupSourceBasis
