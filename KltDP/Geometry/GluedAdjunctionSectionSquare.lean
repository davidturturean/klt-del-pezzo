import KltDP.Geometry.GluedAdjunctionChartSectionMap

/-!
# A proved original pullback square gives equality of original section maps

Evaluate the actual chart square on an original doubly pulled section.
The accepted naturality and pullback-composition formulas, followed by
the existing open section equivalences, identify the two original maps
on every section. This supplies the section agreement used in descent.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace KltDP.Geometry.GluedAdjunctionSectionSquare

open SchemeModuleOpenPullbackSections SchemeModulePullbackCompSections
open GluedAdjunctionPullbackSectionComp GluedAdjunctionChartSectionMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- A proved square of the original pullback maps gives the same map on
the original sections of every open contained in both chart images. -/
theorem hom_eq_of_square {X Y Z : Scheme.{u}} (j : Y ⟶ X) (l : Z ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion l] (M N : X.Modules) (W : X.Opens)
    (hJ : j ''ᵁ (j ⁻¹ᵁ W) = W)
    (hL : l ''ᵁ (l ⁻¹ᵁ (j ⁻¹ᵁ W)) = j ⁻¹ᵁ W)
    (hComp : (l ≫ j) ''ᵁ ((l ≫ j) ⁻¹ᵁ W) = W)
    (a : (schemeModulePullback j).obj M ⟶ (schemeModulePullback j).obj N)
    (b : (schemeModulePullback (l ≫ j)).obj M ⟶ (schemeModulePullback (l ≫ j)).obj N)
    (hSquare : (schemeModulePullback l).map a ≫ (schemeModulePullbackCompIso l j).hom.app N =
      (schemeModulePullbackCompIso l j).hom.app M ≫ b) :
    hom (l ≫ j) M N W hComp b = hom j M N W hJ a := by
  ext m
  rw [hom_apply, hom_apply]
  let s := pullbackSection l ((schemeModulePullback j).obj M) (j ⁻¹ᵁ W)
    (pullbackSection j M W m)
  have h := congrArg (fun q => q.val.app (op ((l ≫ j) ⁻¹ᵁ W)) s) hSquare
  change ((schemeModulePullbackCompIso l j).hom.app N).val.app (op ((l ≫ j) ⁻¹ᵁ W))
      (((schemeModulePullback l).map a).val.app (op ((l ≫ j) ⁻¹ᵁ W)) s) =
    b.val.app (op ((l ≫ j) ⁻¹ᵁ W))
      (((schemeModulePullbackCompIso l j).hom.app M).val.app (op ((l ≫ j) ⁻¹ᵁ W)) s) at h
  have hMap := pullbackSection_map l a (j ⁻¹ᵁ W) (pullbackSection j M W m)
  have hUnit := comp_unit_section l j M W m
  have hEval :
      ((schemeModulePullbackCompIso l j).hom.app N).val.app (op ((l ≫ j) ⁻¹ᵁ W))
        (pullbackSection l ((schemeModulePullback j).obj N) (j ⁻¹ᵁ W)
          (a.val.app (op (j ⁻¹ᵁ W)) (pullbackSection j M W m))) =
      b.val.app (op ((l ≫ j) ⁻¹ᵁ W)) (pullbackSection (l ≫ j) M W m) :=
    (congrArg (fun z => ((schemeModulePullbackCompIso l j).hom.app N).val.app
      (op ((l ≫ j) ⁻¹ᵁ W)) z) hMap.symm).trans
        (h.trans (congrArg (fun z => b.val.app (op ((l ≫ j) ⁻¹ᵁ W)) z) hUnit))
  have hSections := congrArg (sectionsEquiv (l ≫ j) N ((l ≫ j) ⁻¹ᵁ W) W hComp) hEval
  rw [comp_sectionsEquiv j l N W hJ hL hComp, sectionsEquiv_unit] at hSections
  exact hSections.symm

end KltDP.Geometry.GluedAdjunctionSectionSquare
