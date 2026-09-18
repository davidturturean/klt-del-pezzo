import KltDP.Geometry.AffinizationStructureSheaf

/-!
# The canonical pushforward-O isomorphism is local on the target

The proof keeps the actual restriction of the original morphism. The
canonical section maps on all subordinate opens are obtained by cancelling
the literal restriction-ring isomorphism; the original sheaf basis then
gives the global comparison. No cohomology or connected-fibre premise
is used in this locality statement.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u v

namespace KltDP.Geometry.StructureSheafIsoLocal

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- An isomorphism for the canonical map on a restricted target determines
the original section map on every smaller original open. -/
theorem app_isIso_of_restrict (U V : Y.Opens) (hVU : V ≤ U)
    [IsIso (f ∣_ U).c] : IsIso (f.app V) := by
  let W := U.ι ⁻¹ᵁ V
  have himage : U.ι ''ᵁ W = V := by
    apply Opens.ext
    apply Set.Subset.antisymm
    · exact Set.image_preimage_subset _ _
    · intro y hy
      exact ⟨⟨y, hVU hy⟩, hy, rfl⟩
  have h : IsIso ((f ∣_ U).app W) := inferInstance
  rw [morphismRestrict_app] at h
  letI := h
  letI : IsIso (f.app (U.ι ''ᵁ W)) :=
    IsIso.of_isIso_comp_right _
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W)).op)
  rw [Scheme.app_eq f himage.symm]
  infer_instance

/-- The actual canonical pushforward-O map is an isomorphism if it is so
on the original restrictions to an open cover of the target. -/
theorem c_isIso_of_restrict_cover {ι : Type v} (U : ι → Y.Opens)
    (hU : ⨆ i, U i = ⊤) (hi : ∀ i, IsIso (f ∣_ U i).c) : IsIso f.c := by
  let B := {V : Y.Opens // ∃ i, V ≤ U i}
  have hB : Opens.IsBasis (Set.range (fun V : B => V.1)) := by
    rw [Opens.isBasis_iff_nbhd]
    intro V y hy
    have hycover : y ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hyi⟩ := Opens.mem_iSup.mp hycover
    refine ⟨V ⊓ U i, ⟨⟨V ⊓ U i, ⟨i, inf_le_right⟩⟩, rfl⟩,
      ⟨hy, hyi⟩, inf_le_left⟩
  letI : IsIso (AffinizationStructureSheaf.structureMap f) :=
    TopCat.Sheaf.isIso_of_isIso_basis hB (fun V => by
      obtain ⟨i, hVi⟩ := V.2
      letI := hi i
      exact app_isIso_of_restrict f (U i) V.1 hVi)
  exact (TopCat.Sheaf.forget CommRingCat _).map_isIso
    (AffinizationStructureSheaf.structureMap f)

end KltDP.Geometry.StructureSheafIsoLocal
