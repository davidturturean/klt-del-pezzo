import KltDP.Geometry.RationalFunctionSheaf
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Actual function-field transport under an open immersion

For an open immersion between integral schemes, the generic points
correspond and its map on their actual local rings is an isomorphism.
These pinned Mathlib results construct the function-field isomorphism
below. Its compatibility with actual section maps follows from the
existing stalk-map/germ identity, rather than an assumed rational map.

The pinned `AlgebraicGeometry.FunctionField`, `OpenImmersion`, `Scheme`
and `Topology.Sheaves.Stalks` provide all ingredients. The same actual
generic-point correspondence remains in official Mathlib revision
5aedf732b6987e8c26ab3c9ebc855314f82b045f, FunctionField.lean:61–71.
No new external input or restriction on characteristic is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : Y ⟶ X) [IsOpenImmersion f]

/-- The function-field isomorphism is the actual generic stalk map,
preceded by the proved identification of the target generic point. -/
def functionFieldIso : X.functionField ≅ Y.functionField :=
  X.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isOpenImmersion f).symm) ≪≫
    asIso (f.stalkMap (genericPoint Y))

/-- A nonempty inverse image gives a nonempty original open. -/
theorem nonempty_of_preimage (U : X.Opens) [Nonempty (f ⁻¹ᵁ U)] : Nonempty U := by
  obtain ⟨⟨y, hy⟩⟩ := (inferInstance : Nonempty (f ⁻¹ᵁ U))
  exact ⟨⟨f.base y, hy⟩⟩

/-- Transport of rational germs commutes with the actual section map
of the open immersion whenever its inverse-image open is nonempty. -/
theorem germ_comp_functionFieldIso (U : X.Opens)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    X.germToFunctionField U ≫ (functionFieldIso f).hom =
      f.app U ≫ Y.germToFunctionField (f ⁻¹ᵁ U) := by
  change X.presheaf.germ U (genericPoint X) _ ≫
      (X.presheaf.stalkSpecializes
        (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion f).symm).ge ≫
          f.stalkMap (genericPoint Y)) = _
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
  exact Scheme.stalkMap_germ f U (genericPoint Y)
    (genericPoint_mem_nonempty_open Y (f ⁻¹ᵁ U))

/-- The previous identity, on actual section elements. -/
theorem functionFieldIso_germ (U : X.Opens)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (a : Γ(X, U)) :
    (functionFieldIso f).hom (X.germToFunctionField U a) =
      Y.germToFunctionField (f ⁻¹ᵁ U) (f.app U a) :=
  ConcreteCategory.congr_hom (germ_comp_functionFieldIso f U) a

/-- The image of a nonempty source open is nonempty. -/
theorem nonempty_image (U : Y.Opens) [Nonempty U] : Nonempty (f ''ᵁ U) := by
  obtain ⟨⟨y, hy⟩⟩ := (inferInstance : Nonempty U)
  exact ⟨⟨f.base y, y, hy, rfl⟩⟩

/-- On the actual image-open section isomorphism, rational transport
is precisely the map induced by the open immersion. -/
theorem image_germ_comp_functionFieldIso (U : Y.Opens) [Nonempty U] :
    letI := nonempty_image f U
    X.germToFunctionField (f ''ᵁ U) ≫ (functionFieldIso f).hom =
      (f.appIso U).hom ≫ Y.germToFunctionField U := by
  letI := nonempty_image f U
  letI : Nonempty (f ⁻¹ᵁ (f ''ᵁ U)) := by
    rw [Scheme.Hom.preimage_image_eq]
    infer_instance
  rw [Scheme.Hom.appIso_hom, Category.assoc]
  change X.germToFunctionField (f ''ᵁ U) ≫ (functionFieldIso f).hom =
    f.app (f ''ᵁ U) ≫
      (Y.presheaf.map (eqToHom (Scheme.Hom.preimage_image_eq f U).symm).op ≫
        Y.presheaf.germ U (genericPoint Y) _)
  rw [TopCat.Presheaf.germ_res]
  exact germ_comp_functionFieldIso f (f ''ᵁ U)

/-- The same actual compatibility evaluated on a section. -/
theorem functionFieldIso_image_germ (U : Y.Opens) [Nonempty U]
    (a : Γ(X, f ''ᵁ U)) :
    letI := nonempty_image f U
    (functionFieldIso f).hom (X.germToFunctionField (f ''ᵁ U) a) =
      Y.germToFunctionField U ((f.appIso U).hom a) :=
  ConcreteCategory.congr_hom (image_germ_comp_functionFieldIso f U) a

end KltDP.Geometry.OpenImmersionRational
