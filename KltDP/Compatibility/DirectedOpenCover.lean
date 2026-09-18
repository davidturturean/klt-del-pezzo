/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Bounded adaptation of Mathlib 80cbd0498ab39e21d24d6730b3f932cec672a702,
AlgebraicGeometry/Cover/Directed.lean, to the pinned original open-cover API.
Only small open covers are needed here. Open immersion of transition maps
is derived from their original factorization, so no extra property field
is imposed. No scheme-colimit existence is assumed or introduced.
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.PullbackCarrier

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Cover

variable {X : Scheme.{u}}

/-- A directed original open cover has compatible transition maps, and
every point of an original overlap comes from a common smaller chart. -/
class LocallyDirected (𝒰 : OpenCover.{u} X) [SmallCategory 𝒰.J] where
  trans {i j : 𝒰.J} (hij : i ⟶ j) : 𝒰.obj i ⟶ 𝒰.obj j
  trans_id (i : 𝒰.J) : trans (𝟙 i) = 𝟙 (𝒰.obj i)
  trans_comp {i j k : 𝒰.J} (hij : i ⟶ j) (hjk : j ⟶ k) :
    trans (hij ≫ hjk) = trans hij ≫ trans hjk
  w {i j : 𝒰.J} (hij : i ⟶ j) : trans hij ≫ 𝒰.map j = 𝒰.map i
  directed {i j : 𝒰.J} (x : (pullback (𝒰.map i) (𝒰.map j) : Scheme)) :
    ∃ (k : 𝒰.J) (hki : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.obj k),
      (pullback.lift (trans hki) (trans hkj) (by simp only [w])).base y = x

variable (𝒰 : OpenCover.{u} X) [SmallCategory 𝒰.J] [LocallyDirected 𝒰]

/-- The original transition maps of the directed cover. -/
def trans {i j : 𝒰.J} (hij : i ⟶ j) : 𝒰.obj i ⟶ 𝒰.obj j := LocallyDirected.trans hij

@[simp]
theorem trans_map {i j : 𝒰.J} (hij : i ⟶ j) : trans 𝒰 hij ≫ 𝒰.map j = 𝒰.map i :=
  LocallyDirected.w hij

@[simp]
theorem trans_id (i : 𝒰.J) : trans 𝒰 (𝟙 i) = 𝟙 (𝒰.obj i) := LocallyDirected.trans_id i

@[simp]
theorem trans_comp {i j k : 𝒰.J} (hij : i ⟶ j) (hjk : j ⟶ k) :
    trans 𝒰 (hij ≫ hjk) = trans 𝒰 hij ≫ trans 𝒰 hjk := LocallyDirected.trans_comp hij hjk

instance trans_isOpenImmersion {i j : 𝒰.J} (hij : i ⟶ j) : IsOpenImmersion (trans 𝒰 hij) := by
  haveI : IsOpenImmersion (trans 𝒰 hij ≫ 𝒰.map j) := by rw [trans_map]; infer_instance
  exact IsOpenImmersion.of_comp _ (𝒰.map j)

theorem exists_lift_trans_eq {i j : 𝒰.J} (x : (pullback (𝒰.map i) (𝒰.map j) : Scheme)) :
    ∃ (k : 𝒰.J) (hki : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.obj k),
      (pullback.lift (trans 𝒰 hki) (trans 𝒰 hkj) (by simp)).base y = x :=
  LocallyDirected.directed x

/-- Common smaller charts form an actual open cover of the original overlap. -/
def intersectionOfLocallyDirected (i j : 𝒰.J) :
    (pullback (𝒰.map i) (𝒰.map j) : Scheme).OpenCover :=
  Cover.mkOfCovers (Σ k : 𝒰.J, (k ⟶ i) × (k ⟶ j))
    (fun k => 𝒰.obj k.1)
    (fun k => pullback.lift (trans 𝒰 k.2.1) (trans 𝒰 k.2.2) (by simp))
    (fun x => by
      obtain ⟨k, hki, hkj, y, hy⟩ := exists_lift_trans_eq 𝒰 x
      exact ⟨⟨k, hki, hkj⟩, y, hy⟩)
    (fun k => by
      haveI : IsOpenImmersion
          (pullback.lift (trans 𝒰 k.2.1) (trans 𝒰 k.2.2) (by simp) ≫
            pullback.fst (𝒰.map i) (𝒰.map j)) := by
        rw [pullback.lift_fst]
        infer_instance
      exact IsOpenImmersion.of_comp _ (pullback.fst (𝒰.map i) (𝒰.map j)))

/-- The actual diagram defined by the original chart transitions. -/
def functorOfLocallyDirected : 𝒰.J ⥤ Scheme.{u} where
  obj := 𝒰.obj
  map := trans 𝒰
  map_id := trans_id 𝒰
  map_comp := trans_comp 𝒰

/-- The original chart inclusions as a natural transformation to the base. -/
def functorOfLocallyDirectedHomBase :
    functorOfLocallyDirected 𝒰 ⟶ (Functor.const 𝒰.J).obj X where
  app := 𝒰.map
  naturality i j hij := by
    change trans 𝒰 hij ≫ 𝒰.map j = 𝒰.map i ≫ 𝟙 X
    exact (trans_map 𝒰 hij).trans (Category.comp_id _).symm

/-- The original base scheme is the point of the canonical chart cocone. -/
def coconeOfLocallyDirected : Cocone (functorOfLocallyDirected 𝒰) where
  pt := X
  ι := functorOfLocallyDirectedHomBase 𝒰

/-- Glue original morphisms by checking only the actual directed transitions. -/
def glueMorphismsOfLocallyDirected {Y : Scheme.{u}} (g : ∀ i, 𝒰.obj i ⟶ Y)
    (h : ∀ {i j : 𝒰.J} (hij : i ⟶ j), trans 𝒰 hij ≫ g j = g i) : X ⟶ Y :=
  𝒰.glueMorphisms g (fun i j => by
    apply (intersectionOfLocallyDirected 𝒰 i j).hom_ext
    intro k
    change pullback.lift _ _ _ ≫ (pullback.fst _ _ ≫ g i) =
      pullback.lift _ _ _ ≫ (pullback.snd _ _ ≫ g j)
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    exact (h k.2.1).trans (h k.2.2).symm)

@[simp, reassoc]
theorem map_glueMorphismsOfLocallyDirected {Y : Scheme.{u}} (g : ∀ i, 𝒰.obj i ⟶ Y)
    (h : ∀ {i j : 𝒰.J} (hij : i ⟶ j), trans 𝒰 hij ≫ g j = g i) (i : 𝒰.J) :
    𝒰.map i ≫ glueMorphismsOfLocallyDirected 𝒰 g h = g i :=
  𝒰.ι_glueMorphisms _ _ i

/-- The original base scheme is the colimit of its actual directed cover diagram. -/
def isColimitCoconeOfLocallyDirected : IsColimit (coconeOfLocallyDirected 𝒰) where
  desc s := glueMorphismsOfLocallyDirected 𝒰 s.ι.app (fun {i j} hij => by
    change (functorOfLocallyDirected 𝒰).map hij ≫ s.ι.app j = s.ι.app i
    exact s.w hij)
  fac s i := map_glueMorphismsOfLocallyDirected 𝒰 s.ι.app _ i
  uniq s m hm := by
    apply 𝒰.hom_ext
    intro i
    rw [map_glueMorphismsOfLocallyDirected]
    exact hm i

end AlgebraicGeometry.Scheme.Cover
