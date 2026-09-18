import KltDP.Geometry.GluedAdjunctionSectionSquare

/-!
# Original section agreement from a conjugated refinement equality

Cancel the original source comparison while the category is abstract,
then apply the existing section square for the original open immersions.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionRefinedSectionSquare

private theorem cancel_refinement {C : Type*} [Category C] {S₀ T₀ S T : C}
    (eS : S₀ ≅ S) (eT : T₀ ≅ T) (a : S₀ ⟶ T₀) (b : S ⟶ T)
    (h : eS.inv ≫ a ≫ eT.hom = b) : a ≫ eT.hom = eS.hom ≫ b := by
  calc
    a ≫ eT.hom = eS.hom ≫ (eS.inv ≫ a ≫ eT.hom) := by
      simp only [Iso.hom_inv_id_assoc]
    _ = eS.hom ≫ b := congrArg (fun t => eS.hom ≫ t) h

/-- The proved conjugated equality yields equality of the original section maps. -/
theorem hom_eq_of_refined {X Y Z : Scheme.{u}}
    (j : Y ⟶ X) (l : Z ⟶ Y) (g : Z ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion l] [IsOpenImmersion g] (h : l ≫ j = g)
    (M N : X.Modules) (W : X.Opens)
    (hJ : j ''ᵁ (j ⁻¹ᵁ W) = W) (hG : g ''ᵁ (g ⁻¹ᵁ W) = W)
    (a : (schemeModulePullback j).obj M ⟶ (schemeModulePullback j).obj N)
    (b : (schemeModulePullback g).obj M ⟶ (schemeModulePullback g).obj N)
    (hRefined :
      ((schemeModulePullbackCompIso l j).app M ≪≫
        eqToIso (congrArg (fun q => (schemeModulePullback q).obj M) h)).inv ≫
      (schemeModulePullback l).map a ≫
      ((schemeModulePullbackCompIso l j).app N ≪≫
        eqToIso (congrArg (fun q => (schemeModulePullback q).obj N) h)).hom = b) :
    GluedAdjunctionChartSectionMap.hom g M N W hG b =
      GluedAdjunctionChartSectionMap.hom j M N W hJ a := by
  have hSquare := cancel_refinement
    ((schemeModulePullbackCompIso l j).app M ≪≫
      eqToIso (congrArg (fun q => (schemeModulePullback q).obj M) h))
    ((schemeModulePullbackCompIso l j).app N ≪≫
      eqToIso (congrArg (fun q => (schemeModulePullback q).obj N) h))
    ((schemeModulePullback l).map a) b hRefined
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc] at hSquare
  subst g
  have hW : W ≤ (l ≫ j).opensRange := by
    rw [← hG, Scheme.Hom.image_preimage_eq_opensRange_inter]
    exact inf_le_left
  have hJW := j.preimage_le_preimage_of_le hW
  rw [Scheme.Hom.opensRange_comp, Scheme.Hom.preimage_image_eq] at hJW
  have hL : l ''ᵁ (l ⁻¹ᵁ (j ⁻¹ᵁ W)) = j ⁻¹ᵁ W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inter, inf_eq_right.mpr hJW]
  apply GluedAdjunctionSectionSquare.hom_eq_of_square j l M N W hJ hL hG a b
  simpa only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.assoc] using hSquare

end KltDP.Geometry.GluedAdjunctionRefinedSectionSquare
