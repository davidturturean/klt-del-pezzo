/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

Bounded adaptation of Mathlib 80cbd0498ab39e21d24d6730b3f932cec672a702,
AlgebraicGeometry/Gluing.lean:663-725. The original diagram provides all
overlap maps; the triple transition and cocycle are proved before the
actual pinned Scheme.GlueData is constructed. Small original indices
avoid the upstream universe-shrinking transports.
-/
import KltDP.Compatibility.LocallyDirectedTransitions

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IsLocallyDirected

variable {J : Type u} [SmallCategory J] (F : J ⥤ Scheme.{u})
variable [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
variable [(F ⋙ Scheme.forget).IsLocallyDirected] [Quiver.IsThin J]

/-- The original common-chart inclusion factors through the original overlap. -/
theorem homOfLE_V_ι {i j k : J} (fi : k ⟶ i) (fj : k ⟶ j) :
    (F.obj i).homOfLE (le_iSup_of_le ⟨k, fi, fj⟩ le_rfl) ≫ (V F i j).ι =
      (F.map fi).opensRange.ι :=
  Scheme.homOfLE_ι (F.obj i)
    (le_iSup (fun k : Σ l : J, (l ⟶ i) × (l ⟶ j) => (F.map k.2.1).opensRange)
      ⟨k, fi, fj⟩)

/-- The original lift of a common-chart map is its original range factorization. -/
theorem lift_map {i j k : J} (fi : k ⟶ i) (fj : k ⟶ j)
    (h : Set.range (F.map fi).base ⊆ Set.range (V F i j).ι.base) :
    IsOpenImmersion.lift (V F i j).ι (F.map fi) h =
      (F.map fi).isoOpensRange.hom ≫
        (F.obj i).homOfLE (le_iSup_of_le ⟨k, fi, fj⟩ le_rfl) := by
  rw [← cancel_mono (V F i j).ι, IsOpenImmersion.lift_fac, Category.assoc,
    homOfLE_V_ι F fi fj, Scheme.Hom.isoOpensRange_hom_ι]

/-- Actual glue data for the original locally directed diagram of open immersions. -/
def glueData : Scheme.GlueData where
  J := J
  U j := F.obj j
  V ij := (V F ij.1 ij.2).toScheme
  f i j := (V F i j).ι
  f_id i := V_self F i ▸ (Scheme.topIso _).isIso_hom
  f_hasPullback := inferInstance
  f_open := inferInstance
  t i j := t F i j
  t_id i := t_id F i
  t' i j k := pullback.lift
    (IsOpenImmersion.lift (V F j k).ι (pullback.fst _ _ ≫ tAux F i j) (by
      rintro _ ⟨x, rfl⟩
      obtain ⟨l, fi, fj, fk, α, z, hα, hα₁, hα₂, rfl⟩ := exists_of_pullback_V_V F x
      rw [← Scheme.comp_base_apply, reassoc_of% hα₁, homOfLE_tAux F i j fi fj,
        Iso.hom_inv_id_assoc, Scheme.Opens.range_ι, SetLike.mem_coe]
      exact Opens.mem_iSup.mpr ⟨⟨l, fj, fk⟩, ⟨z, rfl⟩⟩))
    (pullback.fst _ _ ≫ t F i j) (by simp [t])
  t_fac i j k := pullback.lift_snd _ _ _
  cocycle i j k := by
    refine Scheme.hom_ext_of_forall _ _ fun x => ?_
    have hx := exists_of_pullback_V_V F x
    obtain ⟨l, fi, fj, fk, α, z, hα, hα₁, hα₂, e⟩ := hx
    letI := hα
    refine ⟨α.opensRange, ⟨z, e⟩, ?_⟩
    rw [← cancel_mono (pullback.snd _ _), ← cancel_mono (Scheme.Opens.ι _)]
    simp only [t, Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
      limit.lift_π_assoc, cospan_left, IsOpenImmersion.lift_fac, Category.id_comp]
    rw [IsOpenImmersion.comp_lift_assoc]
    simp only [limit.lift_π_assoc, cospan_left, PullbackCone.mk_π_app]
    rw [← cancel_epi α.isoOpensRange.hom]
    simp_rw [Scheme.Hom.isoOpensRange_hom_ι_assoc, IsOpenImmersion.comp_lift_assoc]
    simp only [reassoc_of% hα₁, homOfLE_tAux F i j fi fj,
      Iso.hom_inv_id_assoc, reassoc_of% hα₂]
    simp_rw [lift_map F fj fk, Category.assoc, homOfLE_tAux F j k fj fk,
      Iso.hom_inv_id_assoc]
    simp_rw [lift_map F fk fi, Category.assoc, homOfLE_tAux F k i fk fi,
      Iso.hom_inv_id_assoc, ← Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_inv_comp]
    exact (Scheme.homOfLE_ι _ _).symm

/-- Original diagram arrows commute with the inclusions into the constructed gluing. -/
theorem glueDataι_naturality {i j : J} (f : i ⟶ j) :
    F.map f ≫ (glueData F).ι j = (glueData F).ι i := by
  let q : F.obj i ⟶ (V F i j).toScheme :=
    (F.map (𝟙 i)).isoOpensRange.hom ≫
      (F.obj i).homOfLE (le_iSup_of_le ⟨i, 𝟙 i, f⟩ le_rfl)
  have hq : q ≫ (V F i j).ι = 𝟙 (F.obj i) := by
    dsimp only [q]
    rw [Category.assoc, homOfLE_V_ι F (𝟙 i) f,
      Scheme.Hom.isoOpensRange_hom_ι, F.map_id]
  have hqt : q ≫ tAux F i j = F.map f := by
    dsimp only [q]
    rw [Category.assoc, homOfLE_tAux F i j (𝟙 i) f, Iso.hom_inv_id_assoc]
  have h : tAux F i j ≫ (glueData F).ι j =
      (V F i j).ι ≫ (glueData F).ι i := by
    have h := (glueData F).glue_condition i j
    change t F i j ≫ (V F j i).ι ≫ (glueData F).ι j =
      (V F i j).ι ≫ (glueData F).ι i at h
    rwa [t_ι_assoc] at h
  calc
    _ = (q ≫ tAux F i j) ≫ (glueData F).ι j :=
      congrArg (fun a => a ≫ (glueData F).ι j) hqt.symm
    _ = q ≫ ((V F i j).ι ≫ (glueData F).ι i) := by rw [Category.assoc, h]
    _ = _ := by rw [← Category.assoc, hq, Category.id_comp]

end AlgebraicGeometry.Scheme.IsLocallyDirected
