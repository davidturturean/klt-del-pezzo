import KltDP.Geometry.BirationalAdapters
import KltDP.Geometry.CartierDivisorPullback

/-!
# Birationality and the existing original function-field map

For a morphism already proved to preserve generic points, the source
transport in the existing function-field map is the inverse of the
pinned stalk isomorphism of equal points. Cancelling that isomorphism
identifies the original scheme birationality predicate with invertibility
of its original function-field map. Neither property is supplied as a
new geometric input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.BirationalFunctionField

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) [hf : GenericPointPreserving f]

/-- The existing generic-point transport is the isomorphism between the same original stalks. -/
theorem genericSpecialization_isIso :
    IsIso (Y.presheaf.stalkSpecializes (base_genericPoint_specializes f)) := by
  change IsIso (Y.presheaf.stalkCongr (Inseparable.of_eq hf.base_genericPoint)).inv
  infer_instance

/-- Original scheme birationality is exactly invertibility of its original function-field map. -/
theorem isBirationalScheme_iff_functionFieldMap_isIso :
    IsBirationalScheme f ↔ IsIso (functionFieldMap f) := by
  letI := genericSpecialization_isIso f
  constructor
  · intro h
    letI := h.isIso_stalkMap_genericPoint
    unfold functionFieldMap
    infer_instance
  · intro h
    change IsIso (Y.presheaf.stalkSpecializes (base_genericPoint_specializes f) ≫
      f.stalkMap (genericPoint X)) at h
    letI := h
    refine ⟨hf.base_genericPoint, ?_⟩
    exact IsIso.of_isIso_comp_left
      (Y.presheaf.stalkSpecializes (base_genericPoint_specializes f))
      (f.stalkMap (genericPoint X))

end KltDP.Geometry.BirationalFunctionField
