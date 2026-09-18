import KltDP.Geometry.GluedAdjunctionCommonRefinement
import KltDP.Geometry.GluedAdjunctionSectionNaturality
import KltDP.Geometry.GluedAdjunctionNamedSectionLaws
import KltDP.Geometry.GluedAdjunctionSectionSquare

/-!
# Actual adjunction components on the proved simultaneous chart basis

Every component is the original intrinsic adjunction chart map read on
the original ambient sections through the compiled open section
equivalence. The existing scalar, restriction, and isomorphism lemmas
therefore apply to these original global objects.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace KltDP.Geometry.GluedAdjunctionBasisSectionComponents

open GluedAdjunctionChartBasis

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
  (hI : IdealLocallyPrincipalRegular I)

/-- The image of the original quotient chart is its original preimage open. -/
theorem chart_opensRange (c : Chart f I) : (I.glueData.ι c.U).opensRange = c.sourceOpen := by
  apply TopologicalSpace.Opens.ext
  exact I.range_glueData_ι c.U

/-- Every original subopen of the chart is the image of its original preimage. -/
theorem image_preimage (c : Chart f I) (W : I.glueData.glued.Opens) (hW : W ≤ c.sourceOpen) :
    (I.glueData.ι c.U) ''ᵁ ((I.glueData.ι c.U) ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inter, chart_opensRange, inf_eq_right.mpr hW]

/-- The original intrinsic chart map on the original sections of every original subopen. -/
def hom (c : Chart f I) (W : I.glueData.glued.Opens) (hW : W ≤ c.sourceOpen) :
    (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)).val.obj (op W) →+
      (GluedAdjunctionIntrinsicChart.targetSheaf f I).val.obj (op W) :=
  GluedAdjunctionChartSectionMap.hom (I.glueData.ι c.U)
    (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f))
    (GluedAdjunctionIntrinsicChart.targetSheaf f I) W (image_preimage f I c W hW)
    (GluedAdjunctionCommonRefinement.iso f I hI c).hom

/-- The actual original adjunction component is linear over the original section ring. -/
theorem hom_smul (c : Chart f I) (W : I.glueData.glued.Opens) (hW : W ≤ c.sourceOpen)
    (r : Γ(I.glueData.glued, W))
    (m : (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)).val.obj (op W)) :
    hom f I hI c W hW (r • m) = r • hom f I hI c W hW m := by
  exact GluedAdjunctionNamedSectionLaws.hom_smul (I.glueData.ι c.U)
    (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f))
    (GluedAdjunctionIntrinsicChart.targetSheaf f I) W (image_preimage f I c W hW)
    (GluedAdjunctionCommonRefinement.iso f I hI c).hom
    (hom f I hI c W hW) rfl r m

/-- The actual original component retains the original section restriction maps. -/
theorem hom_res (c : Chart f I) (W V : I.glueData.glued.Opens) (h : V ≤ W)
    (hW : W ≤ c.sourceOpen)
    (m : (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)).val.obj (op W)) :
    hom f I hI c V (h.trans hW)
        ((SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)).val.map (homOfLE h).op m) =
      (GluedAdjunctionIntrinsicChart.targetSheaf f I).val.map (homOfLE h).op
        (hom f I hI c W hW m) := by
  exact GluedAdjunctionNamedSectionLaws.hom_res (I.glueData.ι c.U)
    (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f))
    (GluedAdjunctionIntrinsicChart.targetSheaf f I) W V h
    (image_preimage f I c W hW) (image_preimage f I c V (h.trans hW))
    (GluedAdjunctionCommonRefinement.iso f I hI c).hom
    (hom f I hI c W hW) (hom f I hI c V (h.trans hW)) rfl rfl m

/-- The actual chart isomorphism gives a bijection on every original subopen's sections. -/
theorem hom_bijective (c : Chart f I) (W : I.glueData.glued.Opens) (hW : W ≤ c.sourceOpen) :
    Function.Bijective (hom f I hI c W hW) := by
  exact GluedAdjunctionNamedSectionLaws.hom_bijective (I.glueData.ι c.U)
    (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f))
    (GluedAdjunctionIntrinsicChart.targetSheaf f I) W (image_preimage f I c W hW)
    (GluedAdjunctionCommonRefinement.iso f I hI c) (hom f I hI c W hW) rfl

/-- On the same actual ambient chart, the component is independent of its regular equation. -/
theorem hom_eq_of_U_eq (c e : Chart f I) (h : c.U = e.U)
    (W : I.glueData.glued.Opens) (hW : W ≤ c.sourceOpen) (hW' : W ≤ e.sourceOpen) :
    hom f I hI c W hW = hom f I hI e W hW' := by
  obtain ⟨U, d, hU, hd, hA, hQ⟩ := c
  obtain ⟨V, e, hV, he, hA', hQ'⟩ := e
  dsimp only at h
  subst V
  have heq := GluedAdjunctionCommonRefinement.hom_heq_of_U_eq f I hI
    ⟨U, d, hU, hd, hA, hQ⟩ ⟨U, e, hV, he, hA', hQ'⟩ rfl
  unfold hom
  rw [eq_of_heq heq]

end KltDP.Geometry.GluedAdjunctionBasisSectionComponents
