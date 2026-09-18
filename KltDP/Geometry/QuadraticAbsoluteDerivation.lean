import KltDP.Geometry.QuadraticCoverAlgebra
import Mathlib.RingTheory.Derivation.Basic

/-!
# Extending an actual derivation to the quadratic quotient

An original coefficient derivation and a proposed derivative v of the
original root extend precisely when d(s) = 2t v. The map is constructed
on the existing unique coordinates a + bt in the original quotient.
This supplies the dual coordinate derivations for its absolute Kaehler
basis; no smoothness or differential basis is assumed here.
-/

noncomputable section

universe u

namespace KltDP.Geometry.QuadraticCover

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R]

/-- The actual coordinate formula d(a + bt) = d(a) + t d(b) + bv. -/
def absoluteDerivationLinear (s : R) (d : Derivation k R (CoverAlgebra s))
    (v : CoverAlgebra s) : CoverAlgebra s →ₗ[k] CoverAlgebra s :=
  d.toLinearMap.comp ((constantCoeff s).restrictScalars k) +
    root s • d.toLinearMap.comp ((rootCoeff s).restrictScalars k) +
    v • (IsScalarTower.toAlgHom k R (CoverAlgebra s)).toLinearMap.comp
      ((rootCoeff s).restrictScalars k)

theorem absoluteDerivationLinear_apply (s : R)
    (d : Derivation k R (CoverAlgebra s)) (v x : CoverAlgebra s) :
    absoluteDerivationLinear k R s d v x =
      d (constantCoeff s x) + root s * d (rootCoeff s x) +
        v * algebraMap R (CoverAlgebra s) (rootCoeff s x) := rfl

theorem absoluteDerivationLinear_ofCoeffs (s a b : R)
    (d : Derivation k R (CoverAlgebra s)) (v : CoverAlgebra s) :
    absoluteDerivationLinear k R s d v (ofCoeffs s a b) =
      d a + root s * d b + v * algebraMap R (CoverAlgebra s) b := by
  rw [absoluteDerivationLinear_apply, constantCoeff_ofCoeffs, rootCoeff_ofCoeffs]

/-- The original quadratic relation is exactly the compatibility needed
for the constructed linear map to satisfy the Leibniz rule. -/
theorem absoluteDerivationLinear_leibniz (s : R)
    (d : Derivation k R (CoverAlgebra s)) (v : CoverAlgebra s)
    (h : d s = (2 * root s) * v) (x y : CoverAlgebra s) :
    absoluteDerivationLinear k R s d v (x * y) =
      x * absoluteDerivationLinear k R s d v y +
        y * absoluteDerivationLinear k R s d v x := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, ofCoeffs s a b = x :=
    ⟨constantCoeff s x, rootCoeff s x, ofCoeffs_coefficients s x⟩
  obtain ⟨c, e, rfl⟩ : ∃ c e, ofCoeffs s c e = y :=
    ⟨constantCoeff s y, rootCoeff s y, ofCoeffs_coefficients s y⟩
  rw [ofCoeffs_mul, absoluteDerivationLinear_ofCoeffs,
    absoluteDerivationLinear_ofCoeffs, absoluteDerivationLinear_ofCoeffs]
  simp only [map_add, Derivation.leibniz, Algebra.smul_def, map_mul, ofCoeffs]
  rw [h, ← root_sq s]
  ring

/-- The actual extension on the original quadratic algebra. -/
def absoluteDerivation (s : R) (d : Derivation k R (CoverAlgebra s))
    (v : CoverAlgebra s) (h : d s = (2 * root s) * v) :
    Derivation k (CoverAlgebra s) (CoverAlgebra s) :=
  Derivation.mk' (absoluteDerivationLinear k R s d v) (by
    intro x y
    exact absoluteDerivationLinear_leibniz k R s d v h x y)

theorem absoluteDerivation_ofCoeffs (s a b : R)
    (d : Derivation k R (CoverAlgebra s)) (v : CoverAlgebra s)
    (h : d s = (2 * root s) * v) :
    absoluteDerivation k R s d v h (ofCoeffs s a b) =
      d a + root s * d b + v * algebraMap R (CoverAlgebra s) b :=
  absoluteDerivationLinear_ofCoeffs k R s a b d v

@[simp]
theorem absoluteDerivation_algebraMap (s a : R)
    (d : Derivation k R (CoverAlgebra s)) (v : CoverAlgebra s)
    (h : d s = (2 * root s) * v) :
    absoluteDerivation k R s d v h (algebraMap R (CoverAlgebra s) a) = d a := by
  rw [← ofCoeffs_zero_right s a, absoluteDerivation_ofCoeffs]
  simp only [map_zero, mul_zero, add_zero]

@[simp]
theorem absoluteDerivation_root (s : R)
    (d : Derivation k R (CoverAlgebra s)) (v : CoverAlgebra s)
    (h : d s = (2 * root s) * v) :
    absoluteDerivation k R s d v h (root s) = v := by
  rw [← ofCoeffs_zero_one s, absoluteDerivation_ofCoeffs]
  simp only [map_zero, Derivation.map_one_eq_zero, map_one, mul_zero,
    zero_add, mul_one]

end KltDP.Geometry.QuadraticCover

#check @KltDP.Geometry.QuadraticCover.absoluteDerivation
#print axioms KltDP.Geometry.QuadraticCover.absoluteDerivation
