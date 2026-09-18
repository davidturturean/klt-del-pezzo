/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

Bounded adaptation of Mathlib 80cbd0498ab39e21d24d6730b3f932cec672a702,
AlgebraicGeometry/Gluing.lean:536-617. This constructs the actual overlap
opens and proves compatibility from the original diagram's local directedness.
Index types are small in the original scheme universe; no colimit is assumed.
-/
import KltDP.Compatibility.LocallyDirectedGluingBasics

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IsLocallyDirected

variable {J : Type u} [SmallCategory J] (F : J ⥤ Scheme.{u})
variable [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]

/-- The actual union of all common smaller charts inside the first chart. -/
def V (i j : J) : (F.obj i).Opens :=
  ⨆ (k : Σ k, (k ⟶ i) × (k ⟶ j)), (F.map k.2.1).opensRange

theorem V_self (i : J) : V F i i = ⊤ :=
  top_le_iff.mp (le_iSup_of_le ⟨i, 𝟙 _, 𝟙 _⟩
    (by simp [Scheme.Hom.opensRange_of_isIso]))

variable [(F ⋙ Scheme.forget).IsLocallyDirected]

/-- The locally directed condition on the original scheme point maps. -/
theorem exists_map_eq {i j k : J} (fi : i ⟶ k) (fj : j ⟶ k)
    (xi : F.obj i) (xj : F.obj j) (h : (F.map fi).base xi = (F.map fj).base xj) :
    ∃ (l : J) (fli : l ⟶ i) (flj : l ⟶ j) (x : F.obj l),
      (F.map fli).base x = xi ∧ (F.map flj).base x = xj :=
  (F ⋙ Scheme.forget).exists_map_eq_of_isLocallyDirected fi fj xi xj h

/-- Every original triple-overlap point is covered by a common smaller chart,
with both original projection factorizations retained. -/
theorem exists_of_pullback_V_V {i j k : J}
    (x : (pullback (V F i j).ι (V F i k).ι : Scheme)) :
    ∃ (l : J) (fi : l ⟶ i) (fj : l ⟶ j) (fk : l ⟶ k)
      (α : F.obj l ⟶ pullback (V F i j).ι (V F i k).ι) (z : F.obj l),
      IsOpenImmersion α ∧
      α ≫ pullback.fst _ _ = (F.map fi).isoOpensRange.hom ≫
        (F.obj i).homOfLE (le_iSup_of_le ⟨l, fi, fj⟩ le_rfl) ∧
      α ≫ pullback.snd _ _ = (F.map fi).isoOpensRange.hom ≫
        (F.obj i).homOfLE (le_iSup_of_le ⟨l, fi, fk⟩ le_rfl) ∧
      α.base z = x := by
  obtain ⟨k₁, y₁, hy₁⟩ := Opens.mem_iSup.mp
    ((pullback.fst (V F i j).ι (V F i k).ι).base x).2
  obtain ⟨k₂, y₂, hy₂⟩ := Opens.mem_iSup.mp
    ((pullback.snd (V F i j).ι (V F i k).ι).base x).2
  have heq : (F.map k₁.2.1).base y₁ = (F.map k₂.2.1).base y₂ := by
    rw [hy₁, hy₂]
    exact congrArg (fun q => q.base x)
      (pullback.condition (f := (V F i j).ι) (g := (V F i k).ι))
  obtain ⟨l, hli, hlk, z, hz₁, hz₂⟩ := exists_map_eq F k₁.2.1 k₂.2.1 y₁ y₂ heq
  let α : F.obj l ⟶ pullback (V F i j).ι (V F i k).ι :=
    pullback.lift
      ((F.map (hli ≫ k₁.2.1)).isoOpensRange.hom ≫ (F.obj i).homOfLE
        (le_iSup_of_le ⟨l, hli ≫ k₁.2.1, hli ≫ k₁.2.2⟩ le_rfl))
      ((F.map (hli ≫ k₁.2.1)).isoOpensRange.hom ≫ (F.obj i).homOfLE
        (le_iSup_of_le ⟨l, hli ≫ k₁.2.1, hlk ≫ k₂.2.2⟩ le_rfl))
      (by simp)
  haveI : IsOpenImmersion α := by
    haveI : IsOpenImmersion (α ≫ pullback.fst (V F i j).ι (V F i k).ι) := by
      dsimp only [α]
      rw [pullback.lift_fst]
      infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.fst (V F i j).ι (V F i k).ι)
  have hαz : α.base z = x := by
    apply (pullback.fst (V F i j).ι (V F i k).ι).isOpenEmbedding.injective
    apply (V F i j).ι.isOpenEmbedding.injective
    change (α ≫ pullback.fst (V F i j).ι (V F i k).ι ≫ (V F i j).ι).base z =
      (pullback.fst (V F i j).ι (V F i k).ι ≫ (V F i j).ι).base x
    dsimp only [α]
    rw [pullback.lift_fst_assoc, Category.assoc, Scheme.homOfLE_ι,
      Scheme.Hom.isoOpensRange_hom_ι, F.map_comp, Scheme.comp_base_apply, hz₁]
    exact hy₁
  exact ⟨l, hli ≫ k₁.2.1, hli ≫ k₁.2.2, hlk ≫ k₂.2.2, α, z,
    inferInstance, by simp [α], by simp [α], hαz⟩

variable [Quiver.IsThin J]

/-- Two original chart formulas agree on their actual overlap. -/
theorem fst_inv_eq_snd_inv {i j : J}
    (k₁ k₂ : Σ k : J, (k ⟶ i) × (k ⟶ j)) {U : (F.obj i).Opens}
    (h₁ : (F.map k₁.2.1).opensRange ≤ U) (h₂ : (F.map k₂.2.1).opensRange ≤ U) :
    pullback.fst ((F.obj i).homOfLE h₁) ((F.obj i).homOfLE h₂) ≫
      (F.map k₁.2.1).isoOpensRange.inv ≫ F.map k₁.2.2 =
    pullback.snd ((F.obj i).homOfLE h₁) ((F.obj i).homOfLE h₂) ≫
      (F.map k₂.2.1).isoOpensRange.inv ≫ F.map k₂.2.2 := by
  apply Scheme.hom_ext_of_forall
  intro x
  have hc : pullback.fst ((F.obj i).homOfLE h₁) ((F.obj i).homOfLE h₂) ≫
      (F.map k₁.2.1).isoOpensRange.inv ≫ F.map k₁.2.1 =
      pullback.snd ((F.obj i).homOfLE h₁) ((F.obj i).homOfLE h₂) ≫
      (F.map k₂.2.1).isoOpensRange.inv ≫ F.map k₂.2.1 := by
    simp only [Scheme.Hom.isoOpensRange_inv_comp]
    simpa only [Category.assoc, Scheme.homOfLE_ι] using
      congrArg (fun q => q ≫ U.ι) (pullback.condition
        (f := (F.obj i).homOfLE h₁) (g := (F.obj i).homOfLE h₂))
  obtain ⟨l, hli, hlj, y, hy₁, hy₂⟩ := exists_map_eq F k₁.2.1 k₂.2.1
    ((pullback.fst _ _ ≫ (F.map k₁.2.1).isoOpensRange.inv).base x)
    ((pullback.snd _ _ ≫ (F.map k₂.2.1).isoOpensRange.inv).base x)
    (by simpa only [Scheme.comp_base_apply] using congrArg (fun q => q.base x) hc)
  let α : F.obj l ⟶ pullback ((F.obj i).homOfLE h₁) ((F.obj i).homOfLE h₂) :=
    pullback.lift
      (F.map hli ≫ (F.map k₁.2.1).isoOpensRange.hom)
      (F.map hlj ≫ (F.map k₂.2.1).isoOpensRange.hom)
      (by simp [← cancel_mono U.ι, ← Functor.map_comp,
        Subsingleton.elim (hli ≫ k₁.2.1) (hlj ≫ k₂.2.1)])
  haveI : IsOpenImmersion α := by
    haveI : IsOpenImmersion (α ≫ pullback.fst _ _) := by
      dsimp only [α]
      rw [pullback.lift_fst]
      infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.fst _ _)
  have hαy : α.base y = x := by
    apply (pullback.fst ((F.obj i).homOfLE h₁) ((F.obj i).homOfLE h₂)).isOpenEmbedding.injective
    apply (F.map k₁.2.1).isoOpensRange.inv.isOpenEmbedding.injective
    change (α ≫ pullback.fst _ _ ≫ (F.map k₁.2.1).isoOpensRange.inv).base y =
      (pullback.fst _ _ ≫ (F.map k₁.2.1).isoOpensRange.inv).base x
    simpa only [α, pullback.lift_fst_assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using hy₁
  refine ⟨α.opensRange, ⟨y, hαy⟩, ?_⟩
  rw [← cancel_epi α.isoOpensRange.hom]
  simp [α, ← Functor.map_comp, Subsingleton.elim (hli ≫ k₁.2.2) (hlj ≫ k₂.2.2)]

end AlgebraicGeometry.Scheme.IsLocallyDirected
