import KltDP.Geometry.CartierDivisorPullback
import Mathlib.AlgebraicGeometry.Spec

/-!
# The original generic stalk map of an affine spectrum map

Injectivity of the original ring map gives generic-point preservation.
The induced function-field map restricts to that same ring map, by the
original structure-sheaf stalk naturality square.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SpecFunctionFieldMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S] (φ : R ⟶ S)

/-- An injective ring map carries the source generic point to the target generic point. -/
theorem genericPointPreserving (hφ : Function.Injective φ.hom) :
    GenericPointPreserving (Spec.map φ) := by
  constructor
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap φ.hom ⊥ = ⊥
  exact Ideal.comap_bot_of_injective φ.hom hφ

variable [GenericPointPreserving (Spec.map φ)]

/-- The actual generic map agrees with the original affine coefficient map. -/
theorem map_algebraMap (r : R) :
    functionFieldMap (Spec.map φ) (algebraMap R (Spec R).functionField r) =
      algebraMap S (Spec S).functionField (φ.hom r) := by
  have h : StructureSheaf.toStalk R (genericPoint (Spec R)) ≫
      functionFieldMap (Spec.map φ) =
      φ ≫ StructureSheaf.toStalk S (genericPoint (Spec S)) := by
    unfold functionFieldMap
    rw [← Category.assoc]
    have hs : StructureSheaf.toStalk R (genericPoint (Spec R)) ≫
        (Spec R).presheaf.stalkSpecializes (base_genericPoint_specializes (Spec.map φ)) =
        StructureSheaf.toStalk R ((Spec.map φ).base (genericPoint (Spec S))) :=
      StructureSheaf.toStalk_stalkSpecializes (base_genericPoint_specializes (Spec.map φ))
    rw [hs]
    exact stalkMap_toStalk φ (genericPoint (Spec S))
  exact ConcreteCategory.congr_hom h r

end KltDP.Geometry.SpecFunctionFieldMap
