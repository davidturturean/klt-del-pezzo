import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The native differential basis supplied by actual étale coordinates

The given polynomial-algebra structure is the actual coordinate map. Extend
the pinned polynomial differential basis along that map and apply the pinned
étale Kähler equivalence, whose forward map is the original `mapBaseChange`.
The resulting basis vectors are the differentials of the original coordinates.
No basis or differential-comparison equality is an input.
-/

noncomputable section

namespace KltDP.Geometry.EtaleCoordinateDifferentialBasis

universe u

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] (n : ℕ)
variable [Algebra (MvPolynomial (Fin n) k) A]
variable [hTower : IsScalarTower k (MvPolynomial (Fin n) k) A]
variable [hEtale : Algebra.FormallyEtale (MvPolynomial (Fin n) k) A]

include hTower hEtale in
/-- The basis is derived from the actual formally étale coordinate algebra. -/
def basis : Basis (Fin n) A (KaehlerDifferential k A) :=
  ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).baseChange A).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial (Fin n) k) A)

include hTower hEtale in
/-- Each derived basis vector is the native differential of that coordinate. -/
theorem basis_apply (i : Fin n) :
    basis k A n i =
      KaehlerDifferential.D k A
        (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)) := by
  rw [basis, Basis.map_apply, Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]

end KltDP.Geometry.EtaleCoordinateDifferentialBasis
