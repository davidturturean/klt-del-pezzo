import KltDP.Geometry.SchemeKaehlerOpenRestrictionComp

/-!
# The original restriction comparison on successive unit sections

The accepted restriction-composition adjunction normalization gives the
section formula needed to pass the original chart square to ordinary
restricted module sections. No comparison or new restriction functor is
chosen here.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace KltDP.Geometry.GluedAdjunctionRestrictionUnitSections

open SchemeModuleRestriction SchemeKaehlerOpenRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original comparison carries the two original restriction units to
the original unit for the composite open immersion. -/
theorem comp_unit_section {X Y Z : Scheme.{u}} (j : Y ⟶ X) (l : Z ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion l] (M : X.Modules) (U : X.Opens)
    (m : M.val.obj (op U)) :
    ((restrictionCompIso j l).hom.app M).val.app (op ((l ≫ j) ⁻¹ᵁ U))
      (((restrictionAdjunction l).unit.app ((restriction j).obj M)).val.app (op (j ⁻¹ᵁ U))
        (((restrictionAdjunction j).unit.app M).val.app (op U) m)) =
      ((restrictionAdjunction (l ≫ j)).unit.app M).val.app (op U) m := by
  have h := restrictionCompIso_homEquiv j l M ((restriction (l ≫ j)).obj M) (𝟙 _)
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact congrArg (fun a => a.val.app (op U) m) h

end KltDP.Geometry.GluedAdjunctionRestrictionUnitSections
