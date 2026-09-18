import KltDP.Geometry.GluedAdjunctionChartSectionMap

/-!
# The original chart section maps commute with restriction

The original pulled-section naturality, the original sheaf-map
naturality, and the already compiled open section equivalence give the
restriction law for the section map used by the actual chart basis.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace KltDP.Geometry.GluedAdjunctionSectionNaturality

open SchemeModuleOpenPullbackSections GluedAdjunctionChartSectionMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The section map of the original chart morphism retains the original restriction maps. -/
theorem hom_res {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M N : X.Modules) (W V : X.Opens) (h : V ≤ W)
    (hW : f ''ᵁ (f ⁻¹ᵁ W) = W) (hV : f ''ᵁ (f ⁻¹ᵁ V) = V)
    (a : (schemeModulePullback f).obj M ⟶ (schemeModulePullback f).obj N)
    (m : M.val.obj (op W)) :
    hom f M N V hV a (M.val.map (homOfLE h).op m) =
      N.val.map (homOfLE h).op (hom f M N W hW a m) := by
  rw [hom_apply, hom_apply]
  let i := f.preimage_le_preimage_of_le h
  have hPull := pullbackSection_res f M h m
  have hMap := PresheafOfModules.naturality_apply a.val (homOfLE i).op
    (pullbackSection f M W m)
  have hEval : a.val.app (op (f ⁻¹ᵁ V))
      (pullbackSection f M V (M.val.map (homOfLE h).op m)) =
    ((schemeModulePullback f).obj N).val.map (homOfLE i).op
      (a.val.app (op (f ⁻¹ᵁ W)) (pullbackSection f M W m)) :=
    (congrArg (fun z => a.val.app (op (f ⁻¹ᵁ V)) z) hPull.symm).trans hMap
  exact (congrArg (sectionsEquiv f N (f ⁻¹ᵁ V) V hV) hEval).trans
    (sectionsEquiv_naturality f N hW hV i h _)

end KltDP.Geometry.GluedAdjunctionSectionNaturality
