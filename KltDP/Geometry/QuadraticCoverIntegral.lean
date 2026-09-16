import KltDP.Geometry.AffineQuadraticCover
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Integrality of the original quadratic chart from a nonsquare coefficient

An injective coefficient map between nontrivial rings gives an injective
map of the actual quadratic quotients. This is proved using their original
constant and root coordinates. If the target base is a field and the mapped
branch coefficient has no square root, the existing degree-two criterion
makes its quadratic polynomial irreducible. The original quotient embeds
in that field quotient, hence is a domain, and its actual spectrum is integral.

No domain structure on the quotient, irreducible polynomial, or integral
cover is supplied as an input.
The field need not be the fraction field; a specialization uses the actual
fraction-field map and its library-proved injectivity. Characteristic two is
allowed: only integrality, not separability or smoothness, is concluded.

Reuse: pinned Polynomial.irreducible_of_degree_le_three_of_not_isRoot,
AdjoinRoot.instField, Function.Injective.isDomain and Spec of a domain.
The same degree criterion and quotient construction were checked in official
Mathlib revision 80cbd0498ab39e21d24d6730b3f932cec672a702 (Apache 2.0).
No newer source port or replacement algebra is introduced. The geometric
odd-valuation input and global chart assembly remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry Polynomial

universe u v

namespace KltDP.Geometry.QuadraticCover

section Coefficients

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Nontrivial R] [Nontrivial S]

/-- The original constant coordinate commutes with the actual coefficient map. -/
@[simp]
theorem constantCoeff_baseChangeCoeffHom (s : R) (x : CoverAlgebra s) :
    constantCoeff (algebraMap R S s) (baseChangeCoeffHom (S := S) s x) =
      algebraMap R S (constantCoeff s x) := by
  conv_lhs => rw [← ofCoeffs_coefficients s x]
  rw [baseChangeCoeffHom_ofCoeffs, constantCoeff_ofCoeffs]

/-- The original root coordinate commutes with the actual coefficient map. -/
@[simp]
theorem rootCoeff_baseChangeCoeffHom (s : R) (x : CoverAlgebra s) :
    rootCoeff (algebraMap R S s) (baseChangeCoeffHom (S := S) s x) =
      algebraMap R S (rootCoeff s x) := by
  conv_lhs => rw [← ofCoeffs_coefficients s x]
  rw [baseChangeCoeffHom_ofCoeffs, rootCoeff_ofCoeffs]

/-- Injectivity is derived for the original map of actual quadratic quotients. -/
theorem baseChangeCoeffHom_injective (s : R)
    (hinj : Function.Injective (algebraMap R S)) :
    Function.Injective (baseChangeCoeffHom (S := S) s) := by
  intro x y hxy
  have hc : constantCoeff s x = constantCoeff s y := by
    apply hinj
    have h := congrArg (constantCoeff (algebraMap R S s)) hxy
    simpa only [constantCoeff_baseChangeCoeffHom] using h
  have ht : rootCoeff s x = rootCoeff s y := by
    apply hinj
    have h := congrArg (rootCoeff (algebraMap R S s)) hxy
    simpa only [rootCoeff_baseChangeCoeffHom] using h
  calc
    x = ofCoeffs s (constantCoeff s x) (rootCoeff s x) :=
      (ofCoeffs_coefficients s x).symm
    _ = ofCoeffs s (constantCoeff s y) (rootCoeff s y) := by rw [hc, ht]
    _ = y := ofCoeffs_coefficients s y

end Coefficients

/-- Absence of an actual square root gives irreducibility of the actual polynomial. -/
theorem polynomial_irreducible_of_nonsquare {K : Type*} [Field K]
    (s : K) (hs : ∀ x : K, x ^ 2 ≠ s) : Irreducible (polynomial s) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [polynomial_natDegree]
    decide
  · intro x hx
    apply hs x
    have hzero : x ^ 2 - s = 0 := by
      simpa only [Polynomial.IsRoot, polynomial, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] using hx
    exact sub_eq_zero.mp hzero

/-- The original quotient is a domain whenever its branch coefficient remains
nonsquare in an actual field receiving the base injectively. -/
theorem coverAlgebra_isDomain_of_nonsquare {R : Type*} [CommRing R]
    (K : Type*) [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (s : R)
    (hs : ∀ x : K, x ^ 2 ≠ algebraMap R K s) : IsDomain (CoverAlgebra s) := by
  letI : IsDomain R := Function.Injective.isDomain (algebraMap R K) hinj
  letI : Fact (Irreducible (polynomial (algebraMap R K s))) :=
    ⟨polynomial_irreducible_of_nonsquare _ hs⟩
  exact Function.Injective.isDomain (baseChangeCoeffHom (S := K) s)
    (baseChangeCoeffHom_injective s hinj)

/-- The actual affine scheme, with the original branch equation, is integral. -/
theorem affineScheme_isIntegral_of_nonsquare {R : Type u} [CommRing R]
    (K : Type v) [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (s : R)
    (hs : ∀ x : K, x ^ 2 ≠ algebraMap R K s) : IsIntegral (affineScheme s) := by
  letI : IsDomain (CoverAlgebra s) := coverAlgebra_isDomain_of_nonsquare K hinj s hs
  change IsIntegral (Spec (.of (CoverAlgebra s)))
  infer_instance

/-- Fraction-field specialization uses its actual injective structure map. -/
theorem coverAlgebra_isDomain_of_fractionField_nonsquare {R : Type*}
    [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (s : R)
    (hs : ∀ x : K, x ^ 2 ≠ algebraMap R K s) : IsDomain (CoverAlgebra s) :=
  coverAlgebra_isDomain_of_nonsquare K (IsFractionRing.injective R K) s hs

/-- The actual affine chart is integral if the original coefficient is nonsquare
in the actual fraction field of its base ring. -/
theorem affineScheme_isIntegral_of_fractionField_nonsquare {R : Type u}
    [CommRing R] [IsDomain R] (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K] (s : R)
    (hs : ∀ x : K, x ^ 2 ≠ algebraMap R K s) : IsIntegral (affineScheme s) :=
  affineScheme_isIntegral_of_nonsquare K (IsFractionRing.injective R K) s hs

end KltDP.Geometry.QuadraticCover
