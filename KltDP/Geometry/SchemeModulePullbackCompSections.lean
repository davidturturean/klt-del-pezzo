import KltDP.Geometry.SchemeModulePullbackCoherence

/-!
# The original pullback composition comparison on unit sections

The accepted composite-adjunction normalization determines the original
comparison on the original successive pullback-unit sections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.SchemeModulePullbackCompSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original composition comparison sends the two actual unit maps
to the original unit map for the composite scheme morphism. -/
theorem comp_unit_section {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (m : M.val.obj (op U)) :
    ((schemeModulePullbackCompIso f g).hom.app M).val.app (op ((f ≫ g) ⁻¹ᵁ U))
      (((schemeModulePullbackPushforwardAdjunction f).unit.app
        ((schemeModulePullback g).obj M)).val.app (op (g ⁻¹ᵁ U))
        (((schemeModulePullbackPushforwardAdjunction g).unit.app M).val.app (op U) m)) =
      ((schemeModulePullbackPushforwardAdjunction (f ≫ g)).unit.app M).val.app (op U) m := by
  have h := schemeModulePullbackCompIso_homEquiv_hom f g M
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id,
    Category.comp_id] at h
  exact congrArg (fun a => a.val.app (op U) m) h

end KltDP.Geometry.SchemeModulePullbackCompSections
