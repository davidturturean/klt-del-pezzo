import KltDP.Geometry.SchemeModuleUnitCoherence

/-!
# Pullback of scalar endomorphisms of the structure module

A global section `g` of a scheme `Y` acts on the structure module `O_Y` by
multiplication. Pulling this endomorphism back along `f : X ⟶ Y` and transporting it
through the accepted comparison `f^*O_Y ≅ O_X` gives multiplication by the pulled-back
section `f.appTop g`. The proof uses only the adjunction: both sides correspond, under
`homEquiv`, to morphisms `O_Y ⟶ f_*O_X` that send `1` on `U` to `f.app U (g|_U)`,
respectively to `(f.appTop g)|_{f⁻¹U}`, which agree by naturality of `f.app`.

This is the scalar step in the computation of transition units of pulled-back
trivializations (`F03_RESTRICTION_ADAPTERS.md`, task 8).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Scalar

variable (Y : Scheme.{u})

/-- Multiplication by a global section, as an endomorphism of the structure module. -/
def unitScalarHom (g : Γ(Y, ⊤)) :
    _root_.SheafOfModules.unit Y.ringCatSheaf ⟶ _root_.SheafOfModules.unit Y.ringCatSheaf :=
  (_root_.SheafOfModules.unitHomEquiv _).symm
    (schemeModuleSectionOfTop (_root_.SheafOfModules.unit Y.ringCatSheaf) g)

/-- On sections over `U`, the scalar endomorphism multiplies by the restriction of `g`. -/
theorem unitScalarHom_app (g : Γ(Y, ⊤)) (U : Y.Opens) (r : Γ(Y, U)) :
    (unitScalarHom Y g).val.app (op U) r =
      r * Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op g := rfl

end Scalar

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pulled-back scalar endomorphism, followed by the unit comparison, is the unit
comparison followed by multiplication by the pulled-back section. -/
theorem pullback_unitScalarHom_comp_unitHom (g : Γ(Y, ⊤)) :
    (schemeModulePullback f).map (unitScalarHom Y g) ≫ schemeModulePullbackUnitHom f =
      schemeModulePullbackUnitHom f ≫ unitScalarHom X (f.appTop g) := by
  apply ((schemeModulePullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    schemeModuleUnit_homEquiv]
  apply (_root_.SheafOfModules.unitHomEquiv _).injective
  apply PresheafOfModules.sections_ext
  intro U
  obtain ⟨U⟩ := U
  change f.app U ((unitScalarHom Y g).val.app (op U) (1 : Γ(Y, U))) =
    (unitScalarHom X (f.appTop g)).val.app (op (f ⁻¹ᵁ U)) (f.app U (1 : Γ(Y, U)))
  rw [unitScalarHom_app, unitScalarHom_app, one_mul,
    show f.app U 1 = 1 from (f.app U).hom.map_one, one_mul]
  exact ConcreteCategory.congr_hom (f.naturality ((homOfLE (le_top : U ≤ ⊤)).op : op ⊤ ⟶ op U)) g

/-- Transported through the unit comparison, the pullback of multiplication by `g` is
multiplication by `f.appTop g`. -/
theorem unitIso_inv_pullback_unitScalarHom (g : Γ(Y, ⊤)) :
    (schemeModulePullbackUnitIso f).inv ≫
        (schemeModulePullback f).map (unitScalarHom Y g) ≫ (schemeModulePullbackUnitIso f).hom =
      unitScalarHom X (f.appTop g) := by
  rw [Iso.inv_comp_eq]
  exact pullback_unitScalarHom_comp_unitHom f g

end KltDP.Geometry
