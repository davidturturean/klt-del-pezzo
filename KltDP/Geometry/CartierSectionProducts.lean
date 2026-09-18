import KltDP.Geometry.CartierModuleMultiplication
import KltDP.Geometry.SectionEffectiveCartier
import KltDP.Geometry.SchemeModulePullbackUnit

/-!
# Products and ratios of the original Cartier sections

The original section multiplication already lands in the actual Cartier
module of the sum. Its value in the original function field is the literal
product, so products of section ratios require only the field identity.
No tensor comparison or extra scalar action is introduced here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.SectionMonomialGrowth

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual product of two original global Cartier-module sections. -/
def globalProduct (D E : CartierDivisor X)
    (s : (cartierDivisorModule X D).val.obj (op ⊤))
    (t : (cartierDivisorModule X E).val.obj (op ⊤)) :
    (cartierDivisorModule X (D + E)).val.obj (op ⊤) :=
  cartierSectionMul X D E ⊤ s t

/-- The original rational-value map sends this product to multiplication
in the original function field. -/
theorem rationalValue_globalProduct (D E : CartierDivisor X)
    (s : (cartierDivisorModule X D).val.obj (op ⊤))
    (t : (cartierDivisorModule X E).val.obj (op ⊤)) :
    cartierGlobalSectionRationalValue X (D + E) (globalProduct X D E s t) =
      cartierGlobalSectionRationalValue X D s * cartierGlobalSectionRationalValue X E t :=
  (rationalFunctionSectionsIso X ⊤).hom.hom.map_mul s.val t.val

/-- Multiplication of the actual sections multiplies their actual ratios.
This identity itself also holds when a denominator vanishes. -/
theorem ratio_globalProduct (D E : CartierDivisor X)
    (s s₀ : (cartierDivisorModule X D).val.obj (op ⊤))
    (t t₀ : (cartierDivisorModule X E).val.obj (op ⊤)) :
    cartierGlobalSectionRationalValue X (D + E) (globalProduct X D E s t) /
        cartierGlobalSectionRationalValue X (D + E) (globalProduct X D E s₀ t₀) =
      (cartierGlobalSectionRationalValue X D s / cartierGlobalSectionRationalValue X D s₀) *
        (cartierGlobalSectionRationalValue X E t / cartierGlobalSectionRationalValue X E t₀) := by
  rw [rationalValue_globalProduct, rationalValue_globalProduct]
  exact mul_div_mul_comm _ _ _ _

/-- A product of two original nonzero sections is again nonzero. -/
theorem globalProduct_ne_zero (D E : CartierDivisor X)
    (s : (cartierDivisorModule X D).val.obj (op ⊤))
    (t : (cartierDivisorModule X E).val.obj (op ⊤)) (hs : s ≠ 0) (ht : t ≠ 0) :
    globalProduct X D E s t ≠ 0 := by
  intro h
  have hv := rationalValue_globalProduct X D E s t
  rw [h] at hv
  have hz : cartierGlobalSectionRationalValue X (D + E) 0 = 0 :=
    map_zero (rationalFunctionModuleSectionsEquiv X ⊤)
  exact mul_ne_zero (cartierGlobalSectionRationalValue_ne_zero X D s hs)
    (cartierGlobalSectionRationalValue_ne_zero X E t ht) (hv.symm.trans hz)

/-- Its original compatible family is obtained by restricting the actual
global product to every open. -/
def globalProductFamily (D E : CartierDivisor X)
    (s : (cartierDivisorModule X D).val.obj (op ⊤))
    (t : (cartierDivisorModule X E).val.obj (op ⊤)) :
    (cartierDivisorModule X (D + E)).sections :=
  schemeModuleSectionOfTop _ (globalProduct X D E s t)

end KltDP.Geometry.SectionMonomialGrowth
