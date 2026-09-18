import KltDP.Geometry.CartierSchemePullbackOpenImmersion
import KltDP.Compatibility.SheafTensorNaturality

/-!
# The original fractional-module inclusion under open pullback

The accepted Cartier restriction isomorphism is the sheafified original
fractional-module map. Counit naturality identifies its hom with that map.
Consequently the accepted open pullback isomorphism commutes with the actual
rational-function-module comparison, without a rational scalar correction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsOpenImmersion f]

/-- Sheafification does not change the original fractional restriction map. -/
theorem cartierModuleRestrictionIso_hom (D : CartierDivisor X) :
    (cartierModuleRestrictionIso f D).hom = cartierModuleRestrictionHom f D := by
  simp only [cartierModuleRestrictionIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, KltDP.SheafTensorNaturality.sheafificationForgetIso_hom_naturality,
    Iso.inv_hom_id_assoc]

/-- The original restricted Cartier map factors the original rational map. -/
theorem cartierModuleRestrictionHom_inclusion (D : CartierDivisor X) :
    cartierModuleRestrictionHom f D ≫
        cartierDivisorModuleInclusion Y (cartierRestrictionHom f D) =
      cartierRestrictionToRational f D := by
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  rfl

/-- The accepted restriction isomorphism retains the literal inclusion. -/
theorem cartierModuleRestrictionIso_inclusion (D : CartierDivisor X) :
    (cartierModuleRestrictionIso f D).hom ≫
        cartierDivisorModuleInclusion Y (cartierRestrictionHom f D) =
      (SchemeModuleRestriction.restriction f).map
          (cartierDivisorModuleInclusion X D) ≫ (rationalRestrictionIso f).hom := by
  rw [cartierModuleRestrictionIso_hom, cartierModuleRestrictionHom_inclusion]
  rfl

/-- The actual scheme pullback comparison for rational functions, using
the original image-open restriction and original generic-stalk field map. -/
def rationalModulePullbackIso :
    (schemeModulePullback f).obj (rationalFunctionModule X) ≅
      rationalFunctionModule Y :=
  ((SchemeModuleRestriction.restrictionIsoPullback f).app
    (rationalFunctionModule X)).symm ≪≫ rationalRestrictionIso f

/-- The actual open Cartier pullback isomorphism commutes with the actual
fractional-module inclusions and rational-function pullback. -/
theorem cartierModulePullbackIso_inclusion (D : CartierDivisor X) :
    (cartierModulePullbackIso f D).hom ≫
        cartierDivisorModuleInclusion Y (cartierRestrictionHom f D) =
      (schemeModulePullback f).map (cartierDivisorModuleInclusion X D) ≫
        (rationalModulePullbackIso f).hom := by
  change ((SchemeModuleRestriction.restrictionIsoPullback f).inv.app
      (cartierDivisorModule X D) ≫ (cartierModuleRestrictionIso f D).hom) ≫ _ = _
  rw [Category.assoc, cartierModuleRestrictionIso_inclusion, ← Category.assoc,
    ← (SchemeModuleRestriction.restrictionIsoPullback f).inv.naturality
      (cartierDivisorModuleInclusion X D)]
  simp only [rationalModulePullbackIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Category.assoc]

end KltDP.Geometry.OpenImmersionRational

#check @KltDP.Geometry.OpenImmersionRational.cartierModulePullbackIso_inclusion
#print axioms KltDP.Geometry.OpenImmersionRational.cartierModuleRestrictionIso_hom
#print axioms KltDP.Geometry.OpenImmersionRational.cartierModulePullbackIso_inclusion
