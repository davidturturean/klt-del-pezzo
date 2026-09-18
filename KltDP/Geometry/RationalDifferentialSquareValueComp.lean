import KltDP.Geometry.RationalDifferentialSquareValue

/-!
# Original differential-square evaluation with a separate output coordinate

Normalize module-map composition while its two module objects are abstract.
The concrete canonical-frame caller can then use the original separate
section evaluations without expanding its differential module carriers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.RationalDifferentialSquareValue

open OpenImmersionRational

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance compOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- The same proved original square, evaluated as two original module maps. -/
theorem field_value_of_open_square_comp
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (p : Y ⟶ X) [GenericPointPreserving p]
    (l : Z ⟶ Y) [IsOpenImmersion l] [IsOpenImmersion (l ≫ p)]
    (M : X.Modules) (N : Y.Modules)
    (d : (schemeModulePullback p).obj M ⟶ N)
    (b : N ⟶ rationalFunctionModule Y)
    (c : M ⟶ rationalFunctionModule X)
    (h : (schemeModulePullback l).map (d ≫ b) ≫ (rationalModulePullbackIso l).hom =
      (schemeModulePullbackCompIso l p).hom.app M ≫
        (schemeModulePullback (l ≫ p)).map c ≫ (rationalModulePullbackIso (l ≫ p)).hom)
    (U : X.Opens) [Nonempty U] (s : M.val.obj (op U)) :
    rationalFunctionModuleSectionsEquiv Y (p ⁻¹ᵁ U)
        (b.val.app (op (p ⁻¹ᵁ U))
          (d.val.app (op (p ⁻¹ᵁ U)) (pullbackSection p M U s))) =
      functionFieldMap p
        (rationalFunctionModuleSectionsEquiv X U (c.val.app (op U) s)) := by
  exact field_value_of_open_square p l M (d ≫ b) c h U s

end KltDP.Geometry.RationalDifferentialSquareValue

#print axioms KltDP.Geometry.RationalDifferentialSquareValue.field_value_of_open_square_comp
