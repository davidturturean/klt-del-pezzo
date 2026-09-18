import KltDP.Geometry.SchemeModuleOpenPullbackSections
import KltDP.Geometry.SchemeModulePullbackCompSections

/-!
# The original open section equivalence preserves pullback composition

The existing open section equivalence inverts the literal adjunction-unit
section on every open contained in the chart. Every actual pullback section
therefore arises this way. The already proved original composition formula
on unit sections determines the comparison on every original section.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace KltDP.Geometry.GluedAdjunctionPullbackSectionComp

open SchemeModuleOpenPullbackSections SchemeModulePullbackCompSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- On an open contained in the actual image, the existing section equivalence
inverts the original adjunction unit. -/
theorem sectionsEquiv_unit {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (W : X.Opens) (h : f ''ᵁ (f ⁻¹ᵁ W) = W)
    (m : M.val.obj (op W)) :
    sectionsEquiv f M (f ⁻¹ᵁ W) W h (pullbackSection f M W m) = m := by
  have hs := sectionsEquiv_pulledSection f M W W h le_rfl m
  calc
    _ = M.val.map (homOfLE (show W ≤ W from le_rfl)).op m := hs
    _ = m := by
      change M.val.presheaf.map (𝟙 (op W)) m = m
      rw [CategoryTheory.Functor.map_id]
      rfl

/-- Every original open-pullback section is an original pulled section. -/
theorem pullbackSection_surjective {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (W : X.Opens) (h : f ''ᵁ (f ⁻¹ᵁ W) = W) :
    Function.Surjective (pullbackSection f M W) := by
  intro s
  refine ⟨sectionsEquiv f M (f ⁻¹ᵁ W) W h s, ?_⟩
  apply (sectionsEquiv f M (f ⁻¹ᵁ W) W h).injective
  exact sectionsEquiv_unit f M W h _

/-- The original pullback-composition comparison agrees with the successive
existing section equivalences on every original section of the chart. -/
theorem comp_sectionsEquiv {X Y Z : Scheme.{u}} (j : Y ⟶ X) (l : Z ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion l] (M : X.Modules) (W : X.Opens)
    (hJ : j ''ᵁ (j ⁻¹ᵁ W) = W)
    (hL : l ''ᵁ (l ⁻¹ᵁ (j ⁻¹ᵁ W)) = j ⁻¹ᵁ W)
    (hComp : (l ≫ j) ''ᵁ ((l ≫ j) ⁻¹ᵁ W) = W)
    (s : ((schemeModulePullback l).obj ((schemeModulePullback j).obj M)).val.obj
      (op ((l ≫ j) ⁻¹ᵁ W))) :
    sectionsEquiv (l ≫ j) M ((l ≫ j) ⁻¹ᵁ W) W hComp
        (((schemeModulePullbackCompIso l j).hom.app M).val.app (op ((l ≫ j) ⁻¹ᵁ W)) s) =
      sectionsEquiv j M (j ⁻¹ᵁ W) W hJ
        (sectionsEquiv l ((schemeModulePullback j).obj M)
          (l ⁻¹ᵁ (j ⁻¹ᵁ W)) (j ⁻¹ᵁ W) hL s) := by
  have hs : Function.Surjective (fun m => pullbackSection l ((schemeModulePullback j).obj M)
      (j ⁻¹ᵁ W) (pullbackSection j M W m)) :=
    (pullbackSection_surjective l ((schemeModulePullback j).obj M) (j ⁻¹ᵁ W) hL).comp
      (pullbackSection_surjective j M W hJ)
  obtain ⟨m, rfl⟩ := hs s
  rw [show ((schemeModulePullbackCompIso l j).hom.app M).val.app (op ((l ≫ j) ⁻¹ᵁ W))
      (pullbackSection l ((schemeModulePullback j).obj M) (j ⁻¹ᵁ W)
        (pullbackSection j M W m)) = pullbackSection (l ≫ j) M W m from
      comp_unit_section l j M W m]
  rw [sectionsEquiv_unit, sectionsEquiv_unit, sectionsEquiv_unit]

end KltDP.Geometry.GluedAdjunctionPullbackSectionComp
