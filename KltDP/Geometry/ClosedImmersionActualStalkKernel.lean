import KltDP.Geometry.GluedSubschemeStalkKernel

/-!
# The actual stalk kernel of any closed immersion

The accepted glued-subscheme stalk-kernel proof only uses the original
closed immersion, its section-map kernel, and locality of that actual
kernel ideal sheaf. We apply that same proof to an arbitrary original
closed immersion, preserving its actual stalk map. This allows the
original affine quadratic root-zero inclusion to be used directly.

This is a bounded adaptation of `stalkMap_gluedTo_ker_eq_map`; no new
subscheme, replacement stalk, or supplied principal kernel is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u

namespace KltDP.Geometry

/-- The original closed-immersion stalk kernel is the germ extension of its original affine ideal. -/
theorem closedImmersion_stalkMap_ker_eq_map {Z Y : Scheme.{u}}
    (j : Z ⟶ Y) [IsClosedImmersion j] {z : Z} (U : Y.affineOpens)
    (hy : j.base z ∈ U.1) :
    RingHom.ker (j.stalkMap z).hom =
      (j.ker.ideal U).map (Y.presheaf.germ U.1 (j.base z) hy).hom := by
  apply le_antisymm
  · intro a ha
    obtain ⟨W, hzW, s, rfl⟩ := Y.presheaf.germ_exist (j.base z) a
    have ha' : j.stalkMap z (Y.presheaf.germ W (j.base z) hzW s) = 0 := ha
    rw [Scheme.stalkMap_germ_apply] at ha'
    have h0 : Z.presheaf.germ (j ⁻¹ᵁ W) z hzW (j.app W s) =
        Z.presheaf.germ ⊤ z trivial 0 := by
      rw [ha', map_zero]
    obtain ⟨W', hzW', iU, iV, hW'⟩ :=
      TopCat.Presheaf.germ_eq (V := ⊤) Z.presheaf z hzW trivial _ _ h0
    obtain ⟨V', hV'open, hV'⟩ :=
      (IsClosedImmersion.base_closed (f := j)).toIsEmbedding.toIsInducing.isOpen_iff.mp
        W'.isOpen
    let V'op : Y.Opens := ⟨V', hV'open⟩
    have hyV' : j.base z ∈ V'op := by
      have : z ∈ j.base ⁻¹' V' := by rw [hV']; exact hzW'
      exact this
    have hyU' : j.base z ∈ ((U.1 ⊓ W ⊓ V'op : Y.Opens) : Set Y) := ⟨⟨hy, hzW⟩, hyV'⟩
    obtain ⟨_, ⟨V, hVaff, rfl⟩, hyV, hVle⟩ :=
      (isBasis_affine_open Y).exists_subset_of_mem_open hyU' (U.1 ⊓ W ⊓ V'op).2
    have hVU : V ≤ U.1 := fun x hx => (hVle hx).1.1
    have hVW : V ≤ W := fun x hx => (hVle hx).1.2
    have hVV' : V ≤ V'op := fun x hx => (hVle hx).2
    have hj₁ : j ⁻¹ᵁ V ≤ W' := by
      intro w hw
      have : w ∈ j.base ⁻¹' V' := hVV' hw
      show w ∈ (W' : Set Z)
      rw [← hV']
      exact this
    have hmem : Y.presheaf.map (homOfLE hVW).op s ∈ RingHom.ker (j.app V).hom := by
      rw [RingHom.mem_ker]
      have hnat : j.app V (Y.presheaf.map (homOfLE hVW).op s) =
          Z.presheaf.map ((Opens.map j.base).map (homOfLE hVW)).op
            (j.app W s) :=
        ConcreteCategory.congr_hom (j.naturality ((homOfLE hVW).op : op W ⟶ op V)) s
      have hfac : (Opens.map j.base).map (homOfLE hVW) =
          (homOfLE hj₁ : j ⁻¹ᵁ V ⟶ W') ≫ iU := Subsingleton.elim _ _
      change j.app V (Y.presheaf.map (homOfLE hVW).op s) = 0
      rw [hnat, hfac, op_comp, Functor.map_comp]
      erw [CommRingCat.comp_apply]
      rw [hW', map_zero, map_zero]
    have hker := (Scheme.Hom.ker_apply j ⟨V, hVaff⟩).symm
    change RingHom.ker (j.app V).hom = j.ker.ideal ⟨V, hVaff⟩ at hker
    rw [hker, ← j.ker.map_ideal (U := ⟨V, hVaff⟩) (V := U) hVU] at hmem
    have hgerm := Ideal.mem_map_of_mem (Y.presheaf.germ V (j.base z) hyV).hom hmem
    rw [Ideal.map_map] at hgerm
    have hcomp : (Y.presheaf.germ V (j.base z) hyV).hom.comp
        (Y.presheaf.map (homOfLE hVU).op).hom =
        (Y.presheaf.germ U.1 (j.base z) hy).hom := by
      rw [← CommRingCat.hom_comp]
      exact congrArg CommRingCat.Hom.hom
        (TopCat.Presheaf.germ_res Y.presheaf (homOfLE hVU) (j.base z) hyV)
    have hs : Y.presheaf.germ V (j.base z) hyV (Y.presheaf.map (homOfLE hVW).op s) =
        Y.presheaf.germ W (j.base z) hzW s :=
      Y.presheaf.germ_res_apply (homOfLE hVW) (j.base z) hyV s
    rw [← hcomp, ← hs]
    exact hgerm
  · refine Ideal.map_le_iff_le_comap.mpr fun d hd => ?_
    have happ : j.app U.1 d = 0 := by
      have h := (Scheme.Hom.ker_apply j U).symm
      have : d ∈ RingHom.ker (j.app U.1).hom := by rw [h]; exact hd
      exact this
    show j.stalkMap z (Y.presheaf.germ U.1 (j.base z) hy d) = 0
    rw [Scheme.stalkMap_germ_apply, happ, map_zero]

end KltDP.Geometry

#print axioms KltDP.Geometry.closedImmersion_stalkMap_ker_eq_map
