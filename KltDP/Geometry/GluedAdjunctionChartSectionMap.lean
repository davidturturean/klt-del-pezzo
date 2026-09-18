import KltDP.Geometry.GluedAdjunctionPullbackSectionComp

/-!
# Read the original adjunction chart map on the original module sections

The previously compiled open-pullback section equivalences transport the
actual chart morphism to an additive map on the original sections. The
literal unit-section normalization proves its original scalar-linearity.
An original chart isomorphism gives a bijective original section map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace KltDP.Geometry.GluedAdjunctionChartSectionMap

open SchemeModuleOpenPullbackSections GluedAdjunctionPullbackSectionComp

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
  (M N : X.Modules) (W : X.Opens) (hW : f ''ᵁ (f ⁻¹ᵁ W) = W)

/-- The existing original section equivalence transports the original base-ring scalar. -/
theorem sectionsEquiv_smul (r : Γ(X, W))
    (s : ((schemeModulePullback f).obj N).val.obj (op (f ⁻¹ᵁ W))) :
    sectionsEquiv f N (f ⁻¹ᵁ W) W hW (f.app W r • s) =
      r • sectionsEquiv f N (f ⁻¹ᵁ W) W hW s := by
  obtain ⟨m, rfl⟩ := pullbackSection_surjective f N W hW s
  rw [← pullbackSection_smul, sectionsEquiv_unit, sectionsEquiv_unit]

/-- The actual chart map read through the existing original section equivalences. -/
def hom (a : (schemeModulePullback f).obj M ⟶ (schemeModulePullback f).obj N) :
    M.val.obj (op W) →+ N.val.obj (op W) :=
  (sectionsEquiv f N (f ⁻¹ᵁ W) W hW).toAddMonoidHom.comp
    (((a.val.app (op (f ⁻¹ᵁ W))).hom.toAddMonoidHom).comp
      (sectionsEquiv f M (f ⁻¹ᵁ W) W hW).symm.toAddMonoidHom)

/-- The section map is evaluated by pulling the original section through the literal unit. -/
theorem hom_apply (a : (schemeModulePullback f).obj M ⟶ (schemeModulePullback f).obj N)
    (m : M.val.obj (op W)) :
    hom f M N W hW a m = sectionsEquiv f N (f ⁻¹ᵁ W) W hW
      (a.val.app (op (f ⁻¹ᵁ W)) (pullbackSection f M W m)) := by
  have hm : (sectionsEquiv f M (f ⁻¹ᵁ W) W hW).symm m = pullbackSection f M W m := by
    apply (sectionsEquiv f M (f ⁻¹ᵁ W) W hW).injective
    rw [AddEquiv.apply_symm_apply, sectionsEquiv_unit]
  change sectionsEquiv f N (f ⁻¹ᵁ W) W hW
      (a.val.app (op (f ⁻¹ᵁ W)) ((sectionsEquiv f M (f ⁻¹ᵁ W) W hW).symm m)) = _
  rw [hm]

/-- The transported original section map is linear for the original section ring. -/
theorem hom_smul (a : (schemeModulePullback f).obj M ⟶ (schemeModulePullback f).obj N)
    (r : Γ(X, W)) (m : M.val.obj (op W)) :
    hom f M N W hW a (r • m) = r • hom f M N W hW a m := by
  rw [hom_apply, pullbackSection_smul, (a.val.app (op (f ⁻¹ᵁ W))).hom.map_smul,
    sectionsEquiv_smul, hom_apply]

/-- An actual chart isomorphism gives a bijection on the original section modules. -/
theorem hom_bijective (e : (schemeModulePullback f).obj M ≅ (schemeModulePullback f).obj N) :
    Function.Bijective (hom f M N W hW e.hom) := by
  have he : Function.Bijective (e.hom.val.app (op (f ⁻¹ᵁ W))) :=
    ConcreteCategory.bijective_of_isIso
      ((_root_.SheafOfModules.evaluation Y.ringCatSheaf (op (f ⁻¹ᵁ W))).map e.hom)
  exact (sectionsEquiv f N (f ⁻¹ᵁ W) W hW).bijective.comp
    (he.comp (sectionsEquiv f M (f ⁻¹ᵁ W) W hW).symm.bijective)

end KltDP.Geometry.GluedAdjunctionChartSectionMap
