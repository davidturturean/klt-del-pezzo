/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Bounded adaptation of Mathlib 80cbd0498ab39e21d24d6730b3f932cec672a702,
AlgebraicGeometry/RelativeGluing.lean:28-53 and Cover/Directed.lean.
The original pinned Cover.J/obj/map and explicit scheme .base maps are
retained. Local directedness is derived from original overlap coverage
and actual cartesian squares; no colimit or glued scheme is assumed.
-/
import KltDP.Compatibility.LocallyDirectedGluingBasics
import Mathlib.CategoryTheory.Limits.VanKampen

noncomputable section

open CategoryTheory Limits

universe u v w

namespace AlgebraicGeometry.Scheme.Cover

variable {S : Scheme.{u}} (𝒰 : OpenCover.{u} S)
  [SmallCategory 𝒰.J] [LocallyDirected 𝒰]

/-- Two original chart points with the same image lift to a common
smaller chart, using the actual overlap-cover condition. -/
theorem exists_of_map_eq_map {i j : 𝒰.J}
    (xi : 𝒰.obj i) (xj : 𝒰.obj j)
    (h : (𝒰.map i).base xi = (𝒰.map j).base xj) :
    ∃ (k : 𝒰.J) (fi : k ⟶ i) (fj : k ⟶ j) (x : 𝒰.obj k),
      (trans 𝒰 fi).base x = xi ∧ (trans 𝒰 fj).base x = xj := by
  obtain ⟨z, hzi, hzj⟩ := Scheme.Pullback.exists_preimage_pullback xi xj h
  obtain ⟨k, fi, fj, x, hx⟩ := exists_lift_trans_eq 𝒰 z
  refine ⟨k, fi, fj, x, ?_, ?_⟩
  · have hi := congrArg (pullback.fst (𝒰.map i) (𝒰.map j)).base hx
    rw [← Scheme.comp_base_apply, pullback.lift_fst] at hi
    exact hi.trans hzi
  · have hj := congrArg (pullback.snd (𝒰.map i) (𝒰.map j)).base hx
    rw [← Scheme.comp_base_apply, pullback.lift_snd] at hj
    exact hj.trans hzj

/-- The original underlying-point diagram of a directed open cover is
locally directed in the category of types. -/
instance functorOfLocallyDirected_isLocallyDirected :
    (functorOfLocallyDirected 𝒰 ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj heq := by
    change (trans 𝒰 fi).base xi = (trans 𝒰 fj).base xj at heq
    apply exists_of_map_eq_map 𝒰 xi xj
    calc
      (𝒰.map i).base xi = (𝒰.map k).base ((trans 𝒰 fi).base xi) := by
        rw [← Scheme.comp_base_apply, trans_map]
      _ = (𝒰.map k).base ((trans 𝒰 fj).base xj) := congrArg (𝒰.map k).base heq
      _ = (𝒰.map j).base xj := by
        rw [← Scheme.comp_base_apply, trans_map]

end AlgebraicGeometry.Scheme.Cover

namespace AlgebraicGeometry.Scheme

/-- Cartesian transition squares transport local directedness to the
original source diagram when its transition maps are injective. -/
theorem isLocallyDirected_of_equifibered_of_injective
    {J : Type w} [Category.{v} J] {F G : J ⥤ Scheme.{u}}
    (s : F ⟶ G) [Quiver.IsThin J] (hs : NatTrans.Equifibered s)
    (H : ∀ {i j : J} (hij : i ⟶ j), Function.Injective (F.map hij).base)
    [(G ⋙ Scheme.forget).IsLocallyDirected] :
    (F ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj heq := by
    change (F.map fi).base xi = (F.map fj).base xj at heq
    have hG : (G.map fi).base ((s.app i).base xi) =
        (G.map fj).base ((s.app j).base xj) := by
      calc
        (G.map fi).base ((s.app i).base xi) =
            (s.app k).base ((F.map fi).base xi) := by
          rw [← Scheme.comp_base_apply, ← s.naturality, Scheme.comp_base_apply]
        _ = (s.app k).base ((F.map fj).base xj) := congrArg (s.app k).base heq
        _ = (G.map fj).base ((s.app j).base xj) := by
          rw [← Scheme.comp_base_apply, s.naturality, Scheme.comp_base_apply]
    obtain ⟨l, fli, flj, x, hi, hj⟩ :=
      (G ⋙ Scheme.forget).exists_map_eq_of_isLocallyDirected fi fj
        ((s.app i).base xi) ((s.app j).base xj) hG
    change (G.map fli).base x = (s.app i).base xi at hi
    obtain ⟨z, hzi, hzs⟩ := exists_preimage_of_isPullback (hs fli) xi x hi.symm
    refine ⟨l, fli, flj, z, hzi, ?_⟩
    change (F.map flj).base z = xj
    apply H fj
    calc
      (F.map fj).base ((F.map flj).base z) =
          (F.map fi).base ((F.map fli).base z) := by
        rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply,
          ← F.map_comp, ← F.map_comp,
          show flj ≫ fj = fli ≫ fi from Subsingleton.elim _ _]
      _ = (F.map fi).base xi := congrArg (F.map fi).base hzi
      _ = (F.map fj).base xj := heq

end AlgebraicGeometry.Scheme
