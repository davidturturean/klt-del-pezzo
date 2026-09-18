import KltDP.Geometry.CartierSectionMonomials
import KltDP.Geometry.CartierSectionBaseValues
import KltDP.Geometry.ProjectiveChart

/-!
# Homogeneous polynomial evaluation in the original Cartier sections

Each support monomial has the original homogeneous degree. Its actual
section is multiplied by the original base-field coefficient, and the
finite sum lies in O(nD). The original rational-value map evaluates the
same polynomial, also after normalization by a denominator section.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open KltDP.Geometry.ModuleCohomology
open scoped BigOperators

universe u v

namespace KltDP.Geometry.SectionMonomialGrowth

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]
  {I : Type v} (f : X ⟶ Spec (CommRingCat.of k))

/-- The degree of each actual support monomial is the original homogeneous degree. -/
theorem homogeneous_support_degree (p : MvPolynomial I k) {n : ℕ}
    (hp : p.IsHomogeneous n) (a : p.support) : (a : I →₀ ℕ).degree = n := by
  rw [Finsupp.degree_eq_weight_one]
  exact hp (MvPolynomial.mem_support_iff.mp a.property)

/-- A support monomial as an actual section in the common original degree. -/
def homogeneousMonomialSection (D : CartierDivisor X)
    (s : I → sections (cartierDivisorModule X D))
    (p : MvPolynomial I k) {n : ℕ} (hp : p.IsHomogeneous n) (a : p.support) :
    sections (cartierDivisorModule X (n • D)) :=
  castSection X (congrArg (fun r : ℕ => r • D) (homogeneous_support_degree p hp a))
    (monomialSection X D s a)

theorem rationalValue_homogeneousMonomialSection (D : CartierDivisor X)
    (s : I → sections (cartierDivisorModule X D))
    (p : MvPolynomial I k) {n : ℕ} (hp : p.IsHomogeneous n) (a : p.support) :
    cartierGlobalSectionRationalValue X (n • D) (homogeneousMonomialSection D s p hp a) =
      (a : I →₀ ℕ).prod (fun i r => cartierGlobalSectionRationalValue X D (s i) ^ r) := by
  rw [homogeneousMonomialSection, rationalValue_castSection, rationalValue_monomialSection]

/-- Evaluate the original homogeneous polynomial using the original k-section action. -/
def homogeneousSection (D : CartierDivisor X)
    (s : I → sections (cartierDivisorModule X D))
    (p : MvPolynomial I k) {n : ℕ} (hp : p.IsHomogeneous n) :
    sections (cartierDivisorModule X (n • D)) := by
  classical
  letI := baseSectionsModule f (cartierDivisorModule X (n • D))
  exact ∑ a : p.support,
    let v : sections (cartierDivisorModule X (n • D)) :=
      homogeneousMonomialSection D s p hp a
    p.coeff a • v

/-- The actual section has the value of the same original polynomial. -/
theorem rationalValue_homogeneousSection (D : CartierDivisor X)
    (s : I → sections (cartierDivisorModule X D))
    (p : MvPolynomial I k) {n : ℕ} (hp : p.IsHomogeneous n) :
    cartierGlobalSectionRationalValue X (n • D) (homogeneousSection f D s p hp) =
      MvPolynomial.eval₂ (functionFieldScalar f)
        (fun i => cartierGlobalSectionRationalValue X D (s i)) p := by
  classical
  letI := baseSectionsModule f (cartierDivisorModule X (n • D))
  letI := functionFieldAlgebra f
  calc
    _ = ∑ a : p.support, cartierGlobalSectionRationalValue X (n • D)
        (p.coeff a • homogeneousMonomialSection D s p hp a) :=
      map_sum (rationalValueBaseLinearMap f (n • D)) _ _
    _ = ∑ a : p.support, functionFieldScalar f (p.coeff a) *
        (a : I →₀ ℕ).prod (fun i r => cartierGlobalSectionRationalValue X D (s i) ^ r) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [rationalValue_base_smul, rationalValue_homogeneousMonomialSection]
    _ = _ := by
      rw [MvPolynomial.eval₂_eq]
      exact p.support.sum_coe_sort
        (fun a => functionFieldScalar f (p.coeff a) *
          a.prod (fun i r => cartierGlobalSectionRationalValue X D (s i) ^ r))

/-- Division by the denominator to the original degree evaluates the
same homogeneous polynomial in the actual section ratios. -/
theorem ratio_homogeneousSection (D : CartierDivisor X)
    (s₀ : sections (cartierDivisorModule X D))
    (s : I → sections (cartierDivisorModule X D))
    (p : MvPolynomial I k) {n : ℕ} (hp : p.IsHomogeneous n) :
    cartierGlobalSectionRationalValue X (n • D) (homogeneousSection f D s p hp) /
        cartierGlobalSectionRationalValue X D s₀ ^ n =
      MvPolynomial.eval₂ (functionFieldScalar f)
        (fun i => cartierGlobalSectionRationalValue X D (s i) /
          cartierGlobalSectionRationalValue X D s₀) p := by
  rw [rationalValue_homogeneousSection]
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
    (homogeneous_eval₂_scale hp (functionFieldScalar f)
      (fun i => cartierGlobalSectionRationalValue X D (s i))
      (cartierGlobalSectionRationalValue X D s₀)⁻¹).symm

end KltDP.Geometry.SectionMonomialGrowth
