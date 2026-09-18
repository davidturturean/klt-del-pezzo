/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

Bounded adaptation of Mathlib 80cbd0498ab39e21d24d6730b3f932cec672a702,
AlgebraicGeometry/Gluing.lean:735-765,805,817-828,854-865.
The actual glue data is constructed before deriving HasColimit. The original
diagram objects and maps give the cover; no colimit-existence input is used.
Small original indices avoid the upstream universe-shrinking transports.
-/
import KltDP.Compatibility.LocallyDirectedGlueData

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IsLocallyDirected

variable {J : Type u} [SmallCategory J] (F : J ⥤ Scheme.{u})
variable [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
variable [(F ⋙ Scheme.forget).IsLocallyDirected] [Quiver.IsThin J]

/-- The actual cocone into the scheme constructed by the original glue data. -/
def cocone : Cocone F where
  pt := (glueData F).glued
  ι.app j := (glueData F).ι j
  ι.naturality i j f := by
    change F.map f ≫ (glueData F).ι j = (glueData F).ι i ≫ 𝟙 _
    rw [Category.comp_id]
    exact glueDataι_naturality F f

/-- Compatible morphisms from the original diagram agree on the constructed overlap. -/
theorem cocone_overlap (s : Cocone F) (i j : J) :
    (V F i j).ι ≫ s.ι.app i = tAux F i j ≫ s.ι.app j := by
  apply (Scheme.Opens.iSupOpenCover
    (fun k : Σ k, (k ⟶ i) × (k ⟶ j) => (F.map k.2.1).opensRange)).hom_ext
  intro k
  change (F.obj i).homOfLE (le_iSup_of_le k le_rfl) ≫ (V F i j).ι ≫ s.ι.app i =
    (F.obj i).homOfLE (le_iSup_of_le k le_rfl) ≫ tAux F i j ≫ s.ι.app j
  rw [homOfLE_tAux_assoc, Iso.eq_inv_comp]
  calc
    _ = F.map k.2.1 ≫ s.ι.app i := by
      rw [reassoc_of% (homOfLE_V_ι F k.2.1 k.2.2),
        Scheme.Hom.isoOpensRange_hom_ι_assoc]
    _ = s.ι.app k.1 := s.w k.2.1
    _ = F.map k.2.2 ≫ s.ι.app j := (s.w k.2.2).symm

/-- The actual glued scheme satisfies the colimit universal property of the original diagram. -/
def isColimit : IsColimit (cocone F) where
  desc s := Multicoequalizer.desc (glueData F).toGlueData.diagram s.pt s.ι.app (by
    rintro ⟨i, j⟩
    change (V F i j).ι ≫ s.ι.app i = t F i j ≫ (V F j i).ι ≫ s.ι.app j
    rw [t_ι_assoc]
    exact cocone_overlap F s i j)
  fac s j := by
    change Multicoequalizer.π (glueData F).toGlueData.diagram j ≫ _ = s.ι.app j
    exact Multicoequalizer.π_desc (glueData F).toGlueData.diagram s.pt s.ι.app _ j
  uniq s m hm := by
    apply Multicoequalizer.hom_ext (glueData F).toGlueData.diagram
    intro j
    rw [Multicoequalizer.π_desc]
    exact hm j

/-- Colimit existence follows from the constructed scheme and its proved universal property. -/
instance : HasColimit F := HasColimit.mk ⟨cocone F, isColimit F⟩

/-- The canonical comparison between the constructed gluing and the chosen colimit. -/
def gluedIsoColimit : (glueData F).glued ≅ colimit F :=
  (isColimit F).coconePointUniqueUpToIso (colimit.isColimit F)

@[simp, reassoc]
theorem ι_gluedIsoColimit_hom (i : J) :
    (glueData F).ι i ≫ (gluedIsoColimit F).hom = colimit.ι F i :=
  (isColimit F).comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) i

@[simp, reassoc]
theorem ι_gluedIsoColimit_inv (i : J) :
    colimit.ι F i ≫ (gluedIsoColimit F).inv = (glueData F).ι i :=
  (isColimit F).comp_coconePointUniqueUpToIso_inv (colimit.isColimit F) i

instance (i : J) : IsOpenImmersion (colimit.ι F i) := by
  rw [← ι_gluedIsoColimit_hom F i]
  infer_instance

/-- The original chart maps into the colimit cover all its points. -/
theorem ι_jointly_surjective (x : (colimit F : Scheme)) :
    ∃ (i : J) (xi : F.obj i), (colimit.ι F i).base xi = x := by
  obtain ⟨i, xi, h⟩ := (glueData F).ι_jointly_surjective ((gluedIsoColimit F).inv.base x)
  refine ⟨i, xi, ?_⟩
  apply (gluedIsoColimit F).inv.isOpenEmbedding.injective
  change (colimit.ι F i ≫ (gluedIsoColimit F).inv).base xi = (gluedIsoColimit F).inv.base x
  rw [ι_gluedIsoColimit_inv]
  exact h

/-- The original diagram objects, with their original colimit inclusions, form an open cover. -/
def openCover : OpenCover.{u} (colimit F) :=
  Cover.mkOfCovers J F.obj (colimit.ι F) (ι_jointly_surjective F)

@[simp]
theorem openCover_obj (i : J) : (openCover F).obj i = F.obj i := rfl

@[simp]
theorem openCover_map (i : J) : (openCover F).map i = colimit.ι F i := rfl

end AlgebraicGeometry.Scheme.IsLocallyDirected
