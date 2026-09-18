import KltDP.Geometry.CartierSectionFiniteProducts
import Mathlib.Data.Finsupp.Weight

/-!
# Actual Cartier sections for arbitrary monomial exponents

The existing multiplication and powers produce the original section of
O(deg(a)D) for every finitely supported exponent vector a. The construction
uses its actual support list and its value is the literal field monomial.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped BigOperators

universe u v

namespace KltDP.Geometry.SectionMonomialGrowth

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual product of powers along the given finite list. -/
def weightedProduct {I : Type v} (D : CartierDivisor X)
    (s : I → (cartierDivisorModule X D).val.obj (op ⊤)) (a : I → ℕ) :
    (l : List I) → (cartierDivisorModule X ((l.map a).sum • D)).val.obj (op ⊤)
  | [] => castSection X (zero_nsmul D).symm (oneSection X)
  | i :: l => castSection X (add_nsmul D (a i) (l.map a).sum).symm
      (globalProduct X ((a i) • D) ((l.map a).sum • D)
        (sectionPower X D (s i) (a i)) (weightedProduct D s a l))

theorem rationalValue_weightedProduct {I : Type v} (D : CartierDivisor X)
    (s : I → (cartierDivisorModule X D).val.obj (op ⊤)) (a : I → ℕ) (l : List I) :
    cartierGlobalSectionRationalValue X ((l.map a).sum • D)
        (weightedProduct X D s a l) =
      (l.map (fun i => cartierGlobalSectionRationalValue X D (s i) ^ a i)).prod := by
  induction l with
  | nil =>
    simp only [weightedProduct, rationalValue_castSection, rationalValue_oneSection,
      List.map_nil, List.prod_nil]
  | cons i l ih =>
    simp only [weightedProduct, rationalValue_castSection, rationalValue_globalProduct,
      rationalValue_sectionPower, ih, List.map_cons, List.prod_cons]

/-- The original support list has exactly the total degree of its exponent vector. -/
theorem supportList_degree {I : Type v} (a : I →₀ ℕ) :
    (a.support.toList.map (fun i => a i)).sum = a.degree :=
  a.support.sum_map_toList (fun i => a i)

/-- The actual coefficient-one monomial section in its original Cartier degree. -/
def monomialSection {I : Type v} (D : CartierDivisor X)
    (s : I → (cartierDivisorModule X D).val.obj (op ⊤)) (a : I →₀ ℕ) :
    (cartierDivisorModule X (a.degree • D)).val.obj (op ⊤) :=
  castSection X (congrArg (fun m : ℕ => m • D) (supportList_degree a))
    (weightedProduct X D s (fun i => a i) a.support.toList)

/-- Its actual rational value is the original finitely supported monomial. -/
theorem rationalValue_monomialSection {I : Type v} (D : CartierDivisor X)
    (s : I → (cartierDivisorModule X D).val.obj (op ⊤)) (a : I →₀ ℕ) :
    cartierGlobalSectionRationalValue X (a.degree • D) (monomialSection X D s a) =
      a.prod (fun i n => cartierGlobalSectionRationalValue X D (s i) ^ n) := by
  rw [monomialSection, rationalValue_castSection, rationalValue_weightedProduct]
  exact a.support.prod_map_toList (fun i => cartierGlobalSectionRationalValue X D (s i) ^ a i)

end KltDP.Geometry.SectionMonomialGrowth
