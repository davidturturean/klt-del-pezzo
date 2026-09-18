import KltDP.Geometry.GluedAdjunctionOriginalComponentNormalization

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionCommonRefinement
open GluedAdjunctionChartBasis

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
  (hI : IdealLocallyPrincipalRegular I)

private theorem close_expanded {α : Sort*}
    {expandedSource originalSource expandedTarget originalTarget : α}
    (hSource : expandedSource = originalSource)
    (hComputed : expandedSource = expandedTarget)
    (hTarget : expandedTarget = originalTarget) : originalSource = originalTarget :=
  hSource.symm.trans (hComputed.trans hTarget)

private def refinedHom_eq_proof (c : Chart f I) (r : Γ(X, c.U.1)) :=
  close_expanded
    (GluedAdjunctionCommonRefinementOriginalMaps.refinedHom_expansion f I hI c r)
    (GluedAdjunctionOriginalComponentNormalization.chart_square f I hI c r)
    (GluedAdjunctionCommonRefinementOriginalMaps.iso_hom_expansion f I hI (c.basicOpen r))

/-- The original basic-open square identifies the restricted map with the smaller chart map. -/
theorem refinedHom_eq (c : Chart f I) (r : Γ(X, c.U.1)) :
    refinedHom f I hI c r = (iso f I hI (c.basicOpen r)).hom :=
  refinedHom_eq_proof f I hI c r

/-- At each intersection point, the two actual maps agree after restriction to a
common original principal chart. Heterogeneous equality records the proved equality
of the two original ambient opens; it imposes no compatibility assumption. -/
theorem exists_common_agreement (c e : Chart f I) (x : I.glueData.glued)
    (hx : x ∈ c.sourceOpen ⊓ e.sourceOpen) :
    ∃ (r : Γ(X, c.U.1)) (s : Γ(X, e.U.1)),
      (c.basicOpen r).U = (e.basicOpen s).U ∧ x ∈ (c.basicOpen r).sourceOpen ∧
        HEq (refinedHom f I hI c r) (refinedHom f I hI e s) := by
  obtain ⟨r, s, hrs, hxr⟩ := c.exists_common_basicOpen e x hx
  refine ⟨r, s, hrs, hxr, ?_⟩
  rw [refinedHom_eq, refinedHom_eq]
  exact hom_heq_of_U_eq f I hI (c.basicOpen r) (e.basicOpen s) hrs

end KltDP.Geometry.GluedAdjunctionCommonRefinement
