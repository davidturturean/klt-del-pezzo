import KltDP.Geometry.BirationalFunctionField
import KltDP.Geometry.CartierDivisorPullbackComp

/-!
# Birationality of the original factors of a birational composite

The original function-field maps are injective field homomorphisms. Their
original composite is the function-field map of the composite scheme map.
If this composite is invertible, the pinned injective-composition lemma
makes both field homomorphisms bijective. The existing function-field
criterion then proves birationality of both original scheme morphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalComposition

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open BirationalFunctionField CartierDivisorPullbackComp

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
  (f : X ⟶ Y) (g : Y ⟶ Z) [GenericPointPreserving f] [GenericPointPreserving g]

/-- Both original factors of a birational composite are birational. -/
theorem isBirationalScheme_factors_of_comp (h : IsBirationalScheme (f ≫ g)) :
    IsBirationalScheme f ∧ IsBirationalScheme g := by
  letI : IsIso (functionFieldMap (f ≫ g)) :=
    (isBirationalScheme_iff_functionFieldMap_isIso (f ≫ g)).mp h
  have hbij := ConcreteCategory.bijective_of_isIso (functionFieldMap (f ≫ g))
  rw [functionFieldMap_comp] at hbij
  change Function.Bijective ((functionFieldMap f) ∘ (functionFieldMap g)) at hbij
  have hf : Function.Injective (functionFieldMap f) := (functionFieldMap f).hom.injective
  have hg : Function.Injective (functionFieldMap g) := (functionFieldMap g).hom.injective
  obtain ⟨hf', hg'⟩ := hf.bijective₂_of_surjective hg hbij.surjective
  exact ⟨(isBirationalScheme_iff_functionFieldMap_isIso f).mpr
      ((ConcreteCategory.isIso_iff_bijective (functionFieldMap f)).mpr hf'),
    (isBirationalScheme_iff_functionFieldMap_isIso g).mpr
      ((ConcreteCategory.isIso_iff_bijective (functionFieldMap g)).mpr hg')⟩

/-- In particular the original first scheme morphism is birational. -/
theorem isBirationalScheme_left_of_comp (h : IsBirationalScheme (f ≫ g)) :
    IsBirationalScheme f := (isBirationalScheme_factors_of_comp f g h).1

/-- The original second scheme morphism is also birational. -/
theorem isBirationalScheme_right_of_comp (h : IsBirationalScheme (f ≫ g)) :
    IsBirationalScheme g := (isBirationalScheme_factors_of_comp f g h).2

/-- For generic-point-preserving maps of integral schemes, birationality
of the actual composite is equivalent to birationality of both factors. -/
theorem isBirationalScheme_comp_iff :
    IsBirationalScheme (f ≫ g) ↔ IsBirationalScheme f ∧ IsBirationalScheme g := by
  refine ⟨isBirationalScheme_factors_of_comp f g, ?_⟩
  rintro ⟨hf, hg⟩
  letI : IsIso (functionFieldMap f) :=
    (isBirationalScheme_iff_functionFieldMap_isIso f).mp hf
  letI : IsIso (functionFieldMap g) :=
    (isBirationalScheme_iff_functionFieldMap_isIso g).mp hg
  apply (isBirationalScheme_iff_functionFieldMap_isIso (f ≫ g)).mpr
  rw [functionFieldMap_comp]
  infer_instance

end KltDP.Geometry.BirationalComposition
