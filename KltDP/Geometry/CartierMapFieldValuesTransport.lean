import KltDP.Geometry.CartierRationalCoordinate
import KltDP.Geometry.DominantRationalFunctionSheaf

/-!
# Equality transport of original module-map field values

Both module isomorphisms and module maps remain abstract when equality is
eliminated. The original Cartier coordinates and pullback sections are kept
literal, so this lemma transports no independently chosen scalar or frame.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.CartierMapFieldValuesTransport

open CartierRationalCoordinate

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Transport actual field values through equal original module maps and
equal target Cartier identifications, before specializing either object. -/
theorem field_values_congr
    {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (q : B ⟶ A) [GenericPointPreserving q]
    (DA : CartierDivisor A) (DB : CartierDivisor B)
    (MA : A.Modules) (MB : B.Modules)
    (eA eA' : cartierDivisorModule A DA ≅ MA)
    (eB : cartierDivisorModule B DB ≅ MB)
    (a a' : (schemeModulePullback q).obj MA ⟶ MB)
    (heA : eA' = eA) (ha : a' = a)
    (hvalues : ∀ (T : A.Opens) [Nonempty T] (s : MA.val.obj (op T)),
      rationalFunctionModuleSectionsEquiv B (q ⁻¹ᵁ T)
        ((coordinate B DB MB eB).val.app (op (q ⁻¹ᵁ T))
          (a.val.app (op (q ⁻¹ᵁ T)) (pullbackSection q MA T s))) =
        functionFieldMap q (rationalFunctionModuleSectionsEquiv A T
          ((coordinate A DA MA eA).val.app (op T) s))) :
    ∀ (T : A.Opens) [Nonempty T] (s : MA.val.obj (op T)),
      rationalFunctionModuleSectionsEquiv B (q ⁻¹ᵁ T)
        ((coordinate B DB MB eB).val.app (op (q ⁻¹ᵁ T))
          (a'.val.app (op (q ⁻¹ᵁ T)) (pullbackSection q MA T s))) =
        functionFieldMap q (rationalFunctionModuleSectionsEquiv A T
          ((coordinate A DA MA eA').val.app (op T) s)) := by
  subst eA'
  subst a'
  exact hvalues

end KltDP.Geometry.CartierMapFieldValuesTransport

#check @KltDP.Geometry.CartierMapFieldValuesTransport.field_values_congr
#print axioms KltDP.Geometry.CartierMapFieldValuesTransport.field_values_congr
