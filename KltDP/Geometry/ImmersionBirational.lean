import KltDP.Geometry.BirationalFunctionField
import KltDP.Geometry.SchematicImageGlued
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Generic-point-preserving immersions are birational on the original schemes

Surjectivity on the original generic stalk and injectivity of the original
function-field homomorphism give an actual function-field isomorphism.
The pinned preimmersion and immersion classes supply the stalk-surjectivity
hypothesis. The original schematic-image factor also inherits immersion
by cancellation through its actual closed image inclusion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ImmersionBirational

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Integral

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)

/-- Surjectivity on actual stalks makes a generic-point-preserving map birational. -/
theorem isBirationalScheme_of_surjectiveOnStalks
    [GenericPointPreserving f] [SurjectiveOnStalks f] : IsBirationalScheme f := by
  letI := BirationalFunctionField.genericSpecialization_isIso f
  have hs : Function.Surjective (functionFieldMap f) := by
    change Function.Surjective ((f.stalkMap (genericPoint X)) ∘
      (Y.presheaf.stalkSpecializes (base_genericPoint_specializes f)))
    exact (f.stalkMap_surjective (genericPoint X)).comp
      (ConcreteCategory.bijective_of_isIso
        (Y.presheaf.stalkSpecializes (base_genericPoint_specializes f))).surjective
  apply (BirationalFunctionField.isBirationalScheme_iff_functionFieldMap_isIso f).mpr
  exact (ConcreteCategory.isIso_iff_bijective (functionFieldMap f)).mpr
    ⟨(functionFieldMap f).hom.injective, hs⟩

/-- The pinned preimmersion notion already suffices. -/
theorem isBirationalScheme_of_isPreimmersion
    [GenericPointPreserving f] [IsPreimmersion f] : IsBirationalScheme f :=
  isBirationalScheme_of_surjectiveOnStalks f

/-- Every generic-point-preserving locally closed immersion is birational. -/
theorem isBirationalScheme_of_isImmersion
    [GenericPointPreserving f] [IsImmersion f] : IsBirationalScheme f :=
  isBirationalScheme_of_surjectiveOnStalks f

/-- An actual open immersion of integral schemes is birational; generic-point preservation is derived. -/
theorem isBirationalScheme_of_isOpenImmersion [IsOpenImmersion f] : IsBirationalScheme f := by
  letI : GenericPointPreserving f := ⟨genericPoint_eq_of_isOpenImmersion f⟩
  exact isBirationalScheme_of_surjectiveOnStalks f

/-- A closed immersion preserving the original generic point is birational. -/
theorem isBirationalScheme_of_isClosedImmersion
    [GenericPointPreserving f] [IsClosedImmersion f] : IsBirationalScheme f :=
  isBirationalScheme_of_surjectiveOnStalks f

end Integral

/-- The actual factor into the actual schematic image inherits immersion. -/
theorem toImage_isImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    IsImmersion (SchematicImageGlued.toImage f) := by
  letI : IsImmersion (SchematicImageGlued.toImage f ≫ SchematicImageGlued.inclusion f) := by
    rw [SchematicImageGlued.toImage_inclusion]
    infer_instance
  exact IsImmersion.of_comp (SchematicImageGlued.toImage f) (SchematicImageGlued.inclusion f)

end KltDP.Geometry.ImmersionBirational
