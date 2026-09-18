import KltDP.Geometry.GluedAdjunctionBasisSectionRefinement
import KltDP.Geometry.GluedAdjunctionSectionEqComposition

/-!
# Agreement of the original adjunction section maps on all chart intersections

At every intersection point the pinned affine theorem gives one actual
principal refinement of both charts. The proved original refinement
formula and original equation independence identify the maps there.
Separation of the original target sheaf then gives agreement on every
original common subopen. No compatible-atlas premise is used.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace KltDP.Geometry.GluedAdjunctionSectionAgreement

open GluedAdjunctionChartBasis GluedAdjunctionBasisSectionComponents
open GluedAdjunctionBasisSectionRefinement

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem map_word {α : Sort*} {a b c d : α}
    (hA : b = a) (hB : b = c) (hC : c = d) : a = d :=
  hA.symm.trans (hB.trans hC)

private theorem map_proof_arguments {α : Sort*} {P Q : Prop}
    (F : P → α) (G : Q → α) {p : P} {q : Q}
    (h : F p = G q) (p' : P) (q' : Q) : F p' = G q' :=
  (congrArg F (Subsingleton.elim p' p)).trans
    (h.trans (congrArg G (Subsingleton.elim q q')))

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
  (hI : IdealLocallyPrincipalRegular I)

/-- The original adjunction section maps agree on every original common subopen. -/
theorem hom_eq (c e : Chart f I) (W : I.glueData.glued.Opens)
    (hW : W ≤ c.sourceOpen) (hW' : W ≤ e.sourceOpen) :
    hom f I hI c W hW = hom f I hI e W hW' := by
  ext m
  apply TopCat.Presheaf.IsSheaf.section_ext (GluedAdjunctionIntrinsicChart.targetSheaf f I).isSheaf
  intro x hx
  obtain ⟨r, s, hrs, hxr⟩ := c.exists_common_basicOpen e x ⟨hW hx, hW' hx⟩
  let V := W ⊓ (c.basicOpen r).sourceOpen
  have hVc : V ≤ (c.basicOpen r).sourceOpen := inf_le_right
  have hVe : V ≤ (e.basicOpen s).sourceOpen := by
    change V ≤ I.gluedTo ⁻¹ᵁ (e.basicOpen s).U.1
    rw [← hrs]
    exact hVc
  have hVW : V ≤ W := inf_le_left
  refine ⟨V, hVW, ⟨hx, hxr⟩, ?_⟩
  let mV := (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)).val.map
    (homOfLE hVW).op m
  have hRefC := hom_basicOpen f I hI c r V hVc
  have hBoth := hom_eq_of_U_eq f I hI (c.basicOpen r) (e.basicOpen s) hrs V hVc hVe
  have hRefE := hom_basicOpen f I hI e s V hVe
  have hMaps := map_word hRefC hBoth hRefE
  have hAligned := map_proof_arguments
    (fun hV => hom f I hI c V hV) (fun hV => hom f I hI e V hV)
    (p := hVc.trans (c.basicOpen_le r)) (q := hVe.trans (e.basicOpen_le s))
    hMaps (hVW.trans hW) (hVW.trans hW')
  have hEval := congrArg (fun q => q mV) hAligned
  dsimp only [mV] at hEval
  have hResC := hom_res f I hI c W V hVW hW m
  have hResE := hom_res f I hI e W V hVW hW' m
  close_native_section_eq hResC hEval hResE

end KltDP.Geometry.GluedAdjunctionSectionAgreement
