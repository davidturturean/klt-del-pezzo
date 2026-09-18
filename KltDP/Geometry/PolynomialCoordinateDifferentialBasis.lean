import KltDP.Geometry.EtaleCoordinateDifferentialBasis
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-! Native differential bases from an actual polynomial coordinate isomorphism. -/

noncomputable section

namespace KltDP.Geometry.PolynomialCoordinateDifferentialBasis

universe u

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] (n : ℕ)
variable (e : MvPolynomial (Fin n) k ≃ₐ[k] A)

/-- The basis uses the actual coordinate isomorphism and the original Kähler map. -/
def basis : Basis (Fin n) A (KaehlerDifferential k A) := by
  letI : Algebra (MvPolynomial (Fin n) k) A := e.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin n) k) A :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv e.toRingEquiv
  exact EtaleCoordinateDifferentialBasis.basis k A n

theorem basis_apply (i : Fin n) :
    basis k A n e i = KaehlerDifferential.D k A (e (MvPolynomial.X i)) := by
  letI : Algebra (MvPolynomial (Fin n) k) A := e.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin n) k) A :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv e.toRingEquiv
  exact EtaleCoordinateDifferentialBasis.basis_apply k A n i

end KltDP.Geometry.PolynomialCoordinateDifferentialBasis
