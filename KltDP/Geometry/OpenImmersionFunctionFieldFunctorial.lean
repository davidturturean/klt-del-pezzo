import KltDP.Geometry.OpenImmersionFunctionField

/-!
# Identity and composition for actual function-field restriction

The proofs use the pinned stalk universal property: maps from the actual
generic stalk agree when they agree on all germs. The already proved
germ square reduces the identity and composition laws to the actual
scheme section-map laws. No birational-map or rational-pullback axiom is
introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

/-- Every nonempty target open meets an integral open subscheme: both
contain the corresponding actual generic point. -/
theorem preimage_nonempty (f : Y ⟶ X) [IsOpenImmersion f]
    (U : X.Opens) [Nonempty U] : Nonempty (f ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint Y, ?_⟩⟩
  change f.base (genericPoint Y) ∈ U
  rw [genericPoint_eq_of_isOpenImmersion f]
  exact genericPoint_mem_nonempty_open X U

/-- The actual generic-stalk map of the identity open immersion is
the identity on the original function field. -/
theorem functionFieldIso_id_hom :
    (functionFieldIso (𝟙 X)).hom = 𝟙 X.functionField := by
  apply X.presheaf.stalk_hom_ext
  intro U hxU
  letI : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  letI : Nonempty ((𝟙 X) ⁻¹ᵁ U) := preimage_nonempty (𝟙 X) U
  change X.germToFunctionField U ≫ (functionFieldIso (𝟙 X)).hom =
    X.germToFunctionField U ≫ 𝟙 X.functionField
  rw [germ_comp_functionFieldIso, Scheme.id_app, Category.id_comp, Category.comp_id]
  cases U
  rfl

/-- Actual function-field restriction is contravariantly compatible
with composition of actual open immersions. -/
theorem functionFieldIso_comp_hom (f : Y ⟶ X) (g : Z ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (functionFieldIso (g ≫ f)).hom =
      (functionFieldIso f).hom ≫ (functionFieldIso g).hom := by
  apply X.presheaf.stalk_hom_ext
  intro U hxU
  letI : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  letI : Nonempty (f ⁻¹ᵁ U) := preimage_nonempty f U
  letI : Nonempty (g ⁻¹ᵁ (f ⁻¹ᵁ U)) := preimage_nonempty g (f ⁻¹ᵁ U)
  letI : Nonempty ((g ≫ f) ⁻¹ᵁ U) := preimage_nonempty (g ≫ f) U
  change X.germToFunctionField U ≫ (functionFieldIso (g ≫ f)).hom =
    X.germToFunctionField U ≫ ((functionFieldIso f).hom ≫ (functionFieldIso g).hom)
  calc
    _ = (g ≫ f).app U ≫ Z.germToFunctionField ((g ≫ f) ⁻¹ᵁ U) :=
      germ_comp_functionFieldIso (g ≫ f) U
    _ = (f.app U ≫ g.app (f ⁻¹ᵁ U)) ≫
        Z.germToFunctionField (g ⁻¹ᵁ (f ⁻¹ᵁ U)) := rfl
    _ = f.app U ≫ (Y.germToFunctionField (f ⁻¹ᵁ U) ≫ (functionFieldIso g).hom) := by
      rw [germ_comp_functionFieldIso g (f ⁻¹ᵁ U), Category.assoc]
    _ = (X.germToFunctionField U ≫ (functionFieldIso f).hom) ≫
        (functionFieldIso g).hom := by
      rw [germ_comp_functionFieldIso f U, Category.assoc]
    _ = _ := Category.assoc _ _ _

/-- Identity transport on actual nonzero rational functions. -/
theorem functionFieldUnitMap_id (a : X.functionFieldˣ) :
    Units.map (functionFieldIso (𝟙 X)).hom.hom.toMonoidHom a = a := by
  apply Units.ext
  change (functionFieldIso (𝟙 X)).hom (a : X.functionField) = (a : X.functionField)
  rw [functionFieldIso_id_hom (X := X)]
  exact CommRingCat.id_apply X.functionField (a : X.functionField)

/-- Composition transport on actual nonzero rational functions. -/
theorem functionFieldUnitMap_comp (f : Y ⟶ X) (g : Z ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] (a : X.functionFieldˣ) :
    Units.map (functionFieldIso (g ≫ f)).hom.hom.toMonoidHom a =
      Units.map (functionFieldIso g).hom.hom.toMonoidHom
        (Units.map (functionFieldIso f).hom.hom.toMonoidHom a) := by
  apply Units.ext
  change (functionFieldIso (g ≫ f)).hom (a : X.functionField) =
    (functionFieldIso g).hom ((functionFieldIso f).hom (a : X.functionField))
  exact ConcreteCategory.congr_hom (functionFieldIso_comp_hom f g) (a : X.functionField)

end KltDP.Geometry.OpenImmersionRational
