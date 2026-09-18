import KltDP.Geometry.AffineFiniteType
import KltDP.Geometry.CartierSectionBaseValues

/-!
# The original affine-section algebra in the original function field

The base map defined through the canonical affine-open immersion is the
restriction of the original structure morphism on global functions.
Its generic germ therefore gives an algebra homomorphism for the same
base-field action used by actual Cartier section values.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))

/-- The canonical affine-section base map is the original structure map
on this actual open, preceded by the canonical base-section comparison. -/
theorem baseToAffineSectionsMap_eq_appLE {U : X.Opens} (hU : IsAffineOpen U) :
    baseToAffineSectionsMap f hU =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U (by simp) := by
  apply Spec.map_injective
  rw [Spec_map_baseToAffineSectionsMap, Spec.map_comp]
  have hbase : (isAffineOpen_top (Spec (CommRingCat.of k))).fromSpec =
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  rw [← hbase]
  exact (IsAffineOpen.Spec_map_appLE_fromSpec f
    (isAffineOpen_top (Spec (CommRingCat.of k))) hU (by simp)).symm

variable [IsIntegral X]

/-- Affine base scalars have exactly the original global generic germ. -/
theorem germ_affineSections_baseScalar {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] (a : k) :
    X.germToFunctionField U ((baseToAffineSectionsMap f hU).hom a) =
      SectionMonomialGrowth.functionFieldScalar f a := by
  rw [baseToAffineSectionsMap_eq_appLE]
  change X.germToFunctionField U
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (baseFieldToGlobalSections f a)) =
    X.germToFunctionField ⊤ (baseFieldToGlobalSections f a)
  exact TopCat.Presheaf.germ_res_apply X.presheaf
    (homOfLE le_top) (genericPoint X) _ _

/-- The original generic germ, with both original base algebra structures. -/
def affineSectionsToFunctionField {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] :
    letI := affineSectionsAlgebra f hU
    letI := SectionMonomialGrowth.functionFieldAlgebra f
    Γ(X, U) →ₐ[k] X.functionField := by
  letI := affineSectionsAlgebra f hU
  letI := SectionMonomialGrowth.functionFieldAlgebra f
  exact { (X.germToFunctionField U).hom with
    commutes' := germ_affineSections_baseScalar f hU }

/-- No regular function on a nonempty original open is lost at the generic point. -/
theorem affineSectionsToFunctionField_injective {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : Function.Injective (affineSectionsToFunctionField f hU) :=
  X.germToFunctionField_injective U

end KltDP.Geometry
