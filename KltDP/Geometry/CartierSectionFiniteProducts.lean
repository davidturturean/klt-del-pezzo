import KltDP.Geometry.CartierSectionProducts
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite products in the original Cartier modules

Every finite tuple of sections of the actual O(D) gives an actual section
of O(nD). The degree casts use equalities of the original Cartier divisors.
The rational-value identity is the ordinary finite product identity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped BigOperators

universe u

namespace KltDP.Geometry.SectionMonomialGrowth

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- Transport of the original section along an equality of its divisors. -/
def castSection {D E : CartierDivisor X} (h : D = E)
    (s : (cartierDivisorModule X D).val.obj (op ⊤)) :
    (cartierDivisorModule X E).val.obj (op ⊤) := h ▸ s

theorem rationalValue_castSection {D E : CartierDivisor X} (h : D = E)
    (s : (cartierDivisorModule X D).val.obj (op ⊤)) :
    cartierGlobalSectionRationalValue X E (castSection X h s) =
      cartierGlobalSectionRationalValue X D s := by
  subst E
  rfl

/-- The original equation-one frame supplies the actual unit section of O(0). -/
def oneSection : (cartierDivisorModule X 0).val.obj (op ⊤) :=
  cartierEquationSectionEquiv X 0 ⊤ 1
    (by rw [ofMul_one, map_zero, map_zero]) 1

theorem rationalValue_oneSection :
    cartierGlobalSectionRationalValue X 0 (oneSection X) = 1 := by
  unfold cartierGlobalSectionRationalValue oneSection
  rw [cartierEquationSectionEquiv_apply_field]
  simp only [map_one, inv_one, Units.val_one, mul_one]

/-- Multiply the original finite tuple in O(D), preserving its exact degree. -/
def finiteProduct (D : CartierDivisor X) : (n : ℕ) →
    (Fin n → (cartierDivisorModule X D).val.obj (op ⊤)) →
      (cartierDivisorModule X (n • D)).val.obj (op ⊤)
  | 0, _ => castSection X (zero_nsmul D).symm (oneSection X)
  | n + 1, s => castSection X (succ_nsmul' D n).symm
      (globalProduct X D (n • D) (s 0)
        (finiteProduct D n (fun i => s i.succ)))

/-- The original generic-point value is the product of the original values. -/
theorem rationalValue_finiteProduct (D : CartierDivisor X) (n : ℕ)
    (s : Fin n → (cartierDivisorModule X D).val.obj (op ⊤)) :
    cartierGlobalSectionRationalValue X (n • D) (finiteProduct X D n s) =
      ∏ i, cartierGlobalSectionRationalValue X D (s i) := by
  induction n with
  | zero =>
    simp only [finiteProduct, rationalValue_castSection, rationalValue_oneSection,
      Fin.prod_univ_zero]
  | succ n ih =>
    simp only [finiteProduct, rationalValue_castSection, rationalValue_globalProduct,
      ih, Fin.prod_univ_succ]

/-- The actual repeated section, in the actual Cartier module O(nD). -/
def sectionPower (D : CartierDivisor X)
    (s : (cartierDivisorModule X D).val.obj (op ⊤)) (n : ℕ) :
    (cartierDivisorModule X (n • D)).val.obj (op ⊤) :=
  finiteProduct X D n (fun _ => s)

theorem rationalValue_sectionPower (D : CartierDivisor X)
    (s : (cartierDivisorModule X D).val.obj (op ⊤)) (n : ℕ) :
    cartierGlobalSectionRationalValue X (n • D) (sectionPower X D s n) =
      cartierGlobalSectionRationalValue X D s ^ n := by
  simp only [sectionPower, rationalValue_finiteProduct, Fin.prod_const]

/-- Every power of the original nonzero denominator remains nonzero. -/
theorem sectionPower_ne_zero (D : CartierDivisor X)
    (s : (cartierDivisorModule X D).val.obj (op ⊤)) (hs : s ≠ 0) (n : ℕ) :
    sectionPower X D s n ≠ 0 := by
  intro h
  have hv := rationalValue_sectionPower X D s n
  rw [h] at hv
  have hz : cartierGlobalSectionRationalValue X (n • D) 0 = 0 :=
    map_zero (rationalFunctionModuleSectionsEquiv X ⊤)
  exact pow_ne_zero n (cartierGlobalSectionRationalValue_ne_zero X D s hs)
    (hv.symm.trans hz)

end KltDP.Geometry.SectionMonomialGrowth
