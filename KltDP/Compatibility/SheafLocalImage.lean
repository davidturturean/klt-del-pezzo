import KltDP.Compatibility.SheafMonoKernel

/-!
# Local membership in an actual subsheaf

For a monomorphism of sheaves of abelian groups, a section that locally
comes from the source already comes from it on the whole open set.
The proof uses separatedness of the actual cokernel sheaf to show that
the section's quotient class is zero, then applies the proved kernel
description for a monomorphism. No sectionwise cokernel formula or global
surjectivity assumption is used.

The local-to-global equality step is the pinned
`TopCat.Presheaf.IsSheaf.section_ext`; its naturality and zero equations
are the actual sheaf morphism and categorical cokernel equations.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Sheaf

variable {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrp.{u} X}
  (φ : F ⟶ G) [Mono φ]

/-- A section locally in the image of an actual sheaf monomorphism is in its image. -/
theorem exists_preimage_of_locally_in_image (U : Opens X) (s : G.val.obj (op U))
    (h : ∀ x ∈ U, ∃ (V : Opens X) (i : V ⟶ U) (r : F.val.obj (op V)),
      x ∈ V ∧ φ.val.app (op V) r = G.val.map i.op s) :
    ∃ r : F.val.obj (op U), φ.val.app (op U) r = s := by
  apply (toQuotientSheaf_app_eq_zero_iff_of_mono φ U s).mp
  apply TopCat.Presheaf.IsSheaf.section_ext (quotientSheaf φ).cond
  intro x hx
  obtain ⟨V, i, r, hxV, hr⟩ := h x hx
  refine ⟨V, i.le, hxV, ?_⟩
  change (quotientSheaf φ).val.map i.op ((toQuotientSheaf φ).val.app (op U) s) =
    (quotientSheaf φ).val.map i.op 0
  rw [map_zero, ← NatTrans.naturality_apply, ← hr]
  exact ConcreteCategory.congr_hom
    (congrArg (fun ψ : F ⟶ quotientSheaf φ => ψ.val.app (op V))
      (toQuotientSheaf_condition φ)) r

end KltDP.Sheaf
