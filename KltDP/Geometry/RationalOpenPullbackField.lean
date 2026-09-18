import KltDP.Geometry.CartierOpenPullbackInclusion

/-!
# The actual field map in the open rational-module comparison

On a nonempty original source open, the pulled-back rational coordinate is
transported by the original generic-stalk field isomorphism. The comparison
with image-open restriction is the original restriction-to-pullback map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsOpenImmersion f]

/-- The rational-module comparison is the original image-open restriction
comparison after the original restriction-to-pullback isomorphism. -/
theorem restrictionIsoPullback_comp_rationalModulePullbackIso :
    ((SchemeModuleRestriction.restrictionIsoPullback f).app
          (rationalFunctionModule X)).hom ≫ (rationalModulePullbackIso f).hom =
      (rationalRestrictionIso f).hom := by
  simp only [rationalModulePullbackIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- This comparison applies the original field map to the actual rational
value of every original nonempty-open section. -/
theorem rationalModulePullbackIso_field (V : Y.Opens) [Nonempty V]
    (s : ((SchemeModuleRestriction.restriction f).obj
      (rationalFunctionModule X)).val.obj (op V)) :
    letI := nonempty_image f V
    rationalFunctionModuleSectionsEquiv Y V
        ((rationalModulePullbackIso f).hom.val.app (op V)
          ((((SchemeModuleRestriction.restrictionIsoPullback f).app
            (rationalFunctionModule X)).hom).val.app (op V) s)) =
      (functionFieldIso f).hom
        (rationalFunctionModuleSectionsEquiv X (f ''ᵁ V) s) := by
  letI := nonempty_image f V
  have h := congrArg
    (fun a : (SchemeModuleRestriction.restriction f).obj (rationalFunctionModule X) ⟶
        rationalFunctionModule Y =>
      rationalFunctionModuleSectionsEquiv Y V (a.val.app (op V) s))
    (restrictionIsoPullback_comp_rationalModulePullbackIso f)
  exact h.trans (rationalRestrictionSectionEquiv_field f V s)

end KltDP.Geometry.OpenImmersionRational

#check @KltDP.Geometry.OpenImmersionRational.rationalModulePullbackIso_field
#print axioms KltDP.Geometry.OpenImmersionRational.rationalModulePullbackIso_field
