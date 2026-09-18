/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

Bounded adaptation of Mathlib 80cbd0498ab39e21d24d6730b3f932cec672a702,
AlgebraicGeometry/Gluing.lean:622-652 and OpenImmersion.lean:703-706.
The transition morphisms are constructed by the pinned original open-cover
gluing and the original open-immersion lift, with their actual formulas.
-/
import KltDP.Compatibility.LocallyDirectedOverlaps

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

@[reassoc]
theorem IsOpenImmersion.comp_lift {X Y Y' Z : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] (g' : Y' ⟶ Y)
    (H : Set.range g.base ⊆ Set.range f.base) :
    g' ≫ IsOpenImmersion.lift f g H =
      IsOpenImmersion.lift f (g' ≫ g) (by
        rintro _ ⟨y, rfl⟩
        exact H ⟨g'.base y, rfl⟩) := by
  simp [← cancel_mono f]

namespace Scheme.IsLocallyDirected

variable {J : Type u} [SmallCategory J] (F : J ⥤ Scheme.{u})
variable [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
variable [(F ⋙ Scheme.forget).IsLocallyDirected] [Quiver.IsThin J]

/-- The actual overlap map to the second chart, glued from the original diagram maps. -/
def tAux (i j : J) : (V F i j).toScheme ⟶ F.obj j :=
  (Scheme.Opens.iSupOpenCover _).glueMorphisms
    (fun k => (F.map k.2.1).isoOpensRange.inv ≫ F.map k.2.2) (fun k₁ k₂ => by
      dsimp only [Scheme.Opens.iSupOpenCover, Scheme.Cover.mkOfCovers]
      exact fst_inv_eq_snd_inv F k₁ k₂ _ _)

@[reassoc]
theorem homOfLE_tAux (i j : J) {k : J} (fi : k ⟶ i) (fj : k ⟶ j) :
    (F.obj i).homOfLE (le_iSup_of_le ⟨k, fi, fj⟩ le_rfl) ≫ tAux F i j =
      (F.map fi).isoOpensRange.inv ≫ F.map fj :=
  (Scheme.Opens.iSupOpenCover (J := Σ k, (k ⟶ i) × (k ⟶ j)) _).ι_glueMorphisms _ _ ⟨k, fi, fj⟩

/-- The actual transition to the reverse overlap. Its image containment is proved
from the original common-chart cover. -/
def t (i j : J) : (V F i j).toScheme ⟶ (V F j i).toScheme :=
  IsOpenImmersion.lift (V F j i).ι (tAux F i j) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨l, y, hy⟩ := (Scheme.Opens.iSupOpenCover
      (fun k : Σ k, (k ⟶ i) × (k ⟶ j) => (F.map k.2.1).opensRange)).exists_eq x
    rw [← hy]
    change ((F.obj i).homOfLE (le_iSup_of_le l le_rfl) ≫ tAux F i j).base y ∈ V F j i
    rw [homOfLE_tAux, Scheme.comp_base_apply]
    exact Opens.mem_iSup.mpr ⟨⟨l.1, l.2.2, l.2.1⟩,
      ⟨(F.map l.2.1).isoOpensRange.inv.base y, rfl⟩⟩)

@[simp, reassoc]
theorem t_ι (i j : J) : t F i j ≫ (V F j i).ι = tAux F i j :=
  IsOpenImmersion.lift_fac _ _ _

/-- On the diagonal, the actual glued overlap map is the original inclusion. -/
theorem tAux_id (i : J) : tAux F i i = (V F i i).ι := by
  apply (Scheme.Opens.iSupOpenCover
    (fun k : Σ k, (k ⟶ i) × (k ⟶ i) => (F.map k.2.1).opensRange)).hom_ext
  intro k
  change (F.obj i).homOfLE (le_iSup_of_le k le_rfl) ≫ tAux F i i =
    (F.obj i).homOfLE (le_iSup_of_le k le_rfl) ≫ (V F i i).ι
  rw [homOfLE_tAux]
  calc
    _ = (F.map k.2.1).opensRange.ι := by
      simpa only [Subsingleton.elim k.2.2 k.2.1] using
        Scheme.Hom.isoOpensRange_inv_comp (F.map k.2.1)
    _ = _ := (Scheme.homOfLE_ι (F.obj i)
      (le_iSup (fun k : Σ l : J, (l ⟶ i) × (l ⟶ i) => (F.map k.2.1).opensRange) k)).symm

/-- The actual lifted transition on the diagonal is the identity. -/
theorem t_id (i : J) : t F i i = 𝟙 _ := by
  apply (cancel_mono (V F i i).ι).1
  exact (t_ι F i i).trans ((tAux_id F i).trans (Category.id_comp _).symm)

end Scheme.IsLocallyDirected

end AlgebraicGeometry
