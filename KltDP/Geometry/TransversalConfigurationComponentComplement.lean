import KltDP.Geometry.TransverseBranchesOfSurfaceConfiguration

/-!
# Ambient crossing equations survive deletion of a component

The existing component-union stalk map is an isomorphism away from the
deleted component. At a remaining crossing the no-triple-point theorem
places the point in that locus. Thus the original ambient parameters and
their product remain the equations of the original embedded reduced union.
This preserves `TransversalConfiguration`; it does not define an SNC class.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (Y : Scheme.{u}) [NoetherianSpace Y] [AlgebraicGeometry.IsReduced Y]
  (C : ↥(irreducibleComponents Y)) {S : Scheme.{u}} (ι : Y ⟶ S)

private theorem componentImage_mem_of_mem
    (D : ↥(irreducibleComponents (componentUnionScheme Y ({C}ᶜ))))
    (z : componentUnionScheme Y ({C}ᶜ)) (hz : z ∈ D.1) :
    (componentUnionInclusion Y ({C}ᶜ)).base z ∈ (componentImage Y ({C}ᶜ) D).1 := by
  rw [← image_componentImage]
  exact ⟨z, hz, rfl⟩

private theorem composite_component_germ_mem
    (D : ↥(irreducibleComponents (componentUnionScheme Y ({C}ᶜ))))
    (z : componentUnionScheme Y ({C}ᶜ))
    (f : S.presheaf.stalk (ι.base ((componentUnionInclusion Y ({C}ᶜ)).base z)))
    (hf : ∀ (U : Y.affineOpens) (hzU : (componentUnionInclusion Y ({C}ᶜ)).base z ∈ U.1),
      (ι.stalkMap ((componentUnionInclusion Y ({C}ᶜ)).base z)).hom f ∈
        (componentChartIdeal Y {componentImage Y ({C}ᶜ) D} U).map
          (Y.presheaf.germ U.1 _ hzU).hom)
    (V : (componentUnionScheme Y ({C}ᶜ)).affineOpens) (hzV : z ∈ V.1) :
    ((componentUnionInclusion Y ({C}ᶜ) ≫ ι).stalkMap z).hom f ∈
      (componentChartIdeal (componentUnionScheme Y ({C}ᶜ)) {D} V).map
        ((componentUnionScheme Y ({C}ᶜ)).presheaf.germ V.1 z hzV).hom := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := (isBasis_affine_open Y).exists_subset_of_mem_open
    (Set.mem_univ ((componentUnionInclusion Y ({C}ᶜ)).base z)) isOpen_univ
  rw [Scheme.stalkMap_comp, CommRingCat.hom_comp]
  apply stalkMap_chartIdeal_le Y ({C}ᶜ) {D} {componentImage Y ({C}ᶜ) D}
    (fun E hE => by
      rw [Set.mem_singleton_iff] at hE
      rw [hE]
      exact Set.mem_singleton _) z ⟨U, hU⟩ hzU V hzV
  exact Ideal.mem_map_of_mem _ (hf ⟨U, hU⟩ hzU)

/-- The original ambient crossing parameters and product kernel survive the
actual component-subunion inclusion at every point off the removed component. -/
theorem transversalCrossing_componentComplement
    (D E : ↥(irreducibleComponents (componentUnionScheme Y ({C}ᶜ))))
    (z : componentUnionScheme Y ({C}ᶜ))
    (hzC : (componentUnionInclusion Y ({C}ᶜ)).base z ∉ C.1)
    (h : TransversalCrossing ι (componentImage Y ({C}ᶜ) D) (componentImage Y ({C}ᶜ) E)
      ((componentUnionInclusion Y ({C}ᶜ)).base z)) :
    TransversalCrossing (componentUnionInclusion Y ({C}ᶜ) ≫ ι) D E z := by
  haveI := isIso_stalkMap_componentUnionInclusion_compl Y C z hzC
  have hinj : Function.Injective ((componentUnionInclusion Y ({C}ᶜ)).stalkMap z).hom :=
    (asIso ((componentUnionInclusion Y ({C}ᶜ)).stalkMap z)).commRingCatIsoToRingEquiv.injective
  obtain ⟨hregular, hdim, f, g, hspan, hker, hf, hg⟩ := h
  refine ⟨hregular, hdim, f, g, hspan, ?_, ?_, ?_⟩
  · rw [Scheme.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.ker_comp_of_injective _ hinj]
    exact hker
  · exact composite_component_germ_mem Y C ι D z f hf
  · exact composite_component_germ_mem Y C ι E z g hg

/-- Deleting any component preserves the existing ambient transversal
configuration. No leaf, tree, or transversality assumption on the subunion
is required: its crossings occur off the removed component by `no_triple`. -/
theorem transversalConfiguration_componentComplement
    (h : TransversalConfiguration ι) :
    TransversalConfiguration (componentUnionInclusion Y ({C}ᶜ) ≫ ι) where
  no_triple D E F z hzD hzE hzF := by
    rcases h.no_triple _ _ _ _
      (componentImage_mem_of_mem Y C D z hzD)
      (componentImage_mem_of_mem Y C E z hzE)
      (componentImage_mem_of_mem Y C F z hzF) with hDE | hDF | hEF
    · exact Or.inl (componentImage_injective Y ({C}ᶜ) hDE)
    · exact Or.inr (Or.inl (componentImage_injective Y ({C}ᶜ) hDF))
    · exact Or.inr (Or.inr (componentImage_injective Y ({C}ᶜ) hEF))
  crossing D E hDE z hzD hzE := by
    have hzD' := componentImage_mem_of_mem Y C D z hzD
    have hzE' := componentImage_mem_of_mem Y C E z hzE
    have hDE' : componentImage Y ({C}ᶜ) D ≠ componentImage Y ({C}ᶜ) E :=
      fun heq => hDE (componentImage_injective Y ({C}ᶜ) heq)
    have hzC : (componentUnionInclusion Y ({C}ᶜ)).base z ∉ C.1 := by
      intro hzC
      rcases h.no_triple _ _ C _ hzD' hzE' hzC with heq | heq | heq
      · exact hDE' heq
      · exact (componentImage_mem Y ({C}ᶜ) D) (Set.mem_singleton_iff.mpr heq)
      · exact (componentImage_mem Y ({C}ᶜ) E) (Set.mem_singleton_iff.mpr heq)
    exact transversalCrossing_componentComplement Y C ι D E z hzC
      (h.crossing _ _ hDE' _ hzD' hzE')

end KltDP.Geometry.RationalTreePicard
