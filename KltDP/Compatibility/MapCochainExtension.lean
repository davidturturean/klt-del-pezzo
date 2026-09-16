/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Vasily Ilin

Adapted from Vilin97/MazurTheorem
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafDerivedGlobalSections.lean,
the mapXIso--mapExtendIso_naturality block. The original complexes and
canonical extension maps are retained at Mathlib c44e0c8e.
-/
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Applying an additive functor commutes with extension of a cochain complex

A nonnegative cochain complex extends to the integers by zero in negative
degrees. Applying the original additive functor before or after extension
gives naturally isomorphic complexes. The component isomorphisms use the
original extension comparisons in nonnegative degrees and the unique maps
between zero objects otherwise.

This is one ordinary prerequisite in the Ext/right-derived comparison.
It asserts no Ext comparison, cohomology finiteness or scalar transport.
Source correspondence: docs/reuse_sources/cohomology_finiteness_next/
derived_comparison_leaf/README.md.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace KltDP.CochainComparison

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G : C ⥤ AddCommGrp.{v}} [G.Additive]

private def mapXIso (K : CochainComplex C ℕ) (n : ℕ) :
    G.obj (K.X n) ≅ ((G.mapHomologicalComplex (.up ℕ)).obj K).X n :=
  Iso.refl _

private lemma mapXIso_naturality (K : CochainComplex C ℕ) (i j : ℕ) :
    (mapXIso K i).hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d i j =
      G.map (K.d i j) ≫ (mapXIso K j).hom :=
  rfl

private def mapExtendXIso
    (K : CochainComplex C ℕ) (n : ℤ) :
    G.obj ((K.extend ComplexShape.embeddingUpNat).X n) ≅
      (((G.mapHomologicalComplex (.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat).X n := by
  classical
  exact if h : 0 ≤ n then
      G.mapIso (HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
        (Int.toNat_of_nonneg h)) ≪≫
        mapXIso K n.toNat ≪≫
        (HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
          ComplexShape.embeddingUpNat (Int.toNat_of_nonneg h)).symm
    else
      IsZero.iso
        (G.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat n
          (fun k hk ↦ h (hk ▸ Int.natCast_nonneg k))))
        (((G.mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X
          ComplexShape.embeddingUpNat n (fun k hk ↦ h (hk ▸ Int.natCast_nonneg k)))

private lemma mapExtendXIso_natCast (K : CochainComplex C ℕ) (k : ℕ) :
    mapExtendXIso (G := G) K (k : ℤ) =
      G.mapIso (HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f k)) ≪≫
        mapXIso (G := G) K k ≪≫
          (HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
            ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)).symm := by
  classical
  simp [mapExtendXIso]

def mapExtendIso (K : CochainComplex C ℕ) :
    (G.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((G.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents (mapExtendXIso K) fun i j hij ↦ by
    clear hij
    by_cases hi : ∃ k, ComplexShape.embeddingUpNat.f k = i
    · obtain ⟨a, ha⟩ := hi
      have ha' : (a : ℤ) = i := (ComplexShape.embeddingUpNat_f a).symm.trans ha
      clear ha
      subst i
      by_cases hj : ∃ k, ComplexShape.embeddingUpNat.f k = j
      · obtain ⟨b, hb⟩ := hj
        have hb' : (b : ℤ) = j := (ComplexShape.embeddingUpNat_f b).symm.trans hb
        clear hb
        subst j
        rw [mapExtendXIso_natCast (G := G) K a, mapExtendXIso_natCast (G := G) K b]
        rw [Functor.mapHomologicalComplex_obj_d,
          HomologicalComplex.extend_d_eq ((G.mapHomologicalComplex (.up ℕ)).obj K)
            ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f a)
              (ComplexShape.embeddingUpNat_f b),
          HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat
            (ComplexShape.embeddingUpNat_f a) (ComplexShape.embeddingUpNat_f b)]
        let eᵢ := HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
          (ComplexShape.embeddingUpNat_f a)
        let eⱼ := HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
          (ComplexShape.embeddingUpNat_f b)
        let fᵢ := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f a)
        let fⱼ := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f b)
        let mᵢ := mapXIso (G := G) K a
        let mⱼ := mapXIso (G := G) K b
        change (G.map eᵢ.hom ≫ mᵢ.hom ≫ fᵢ.inv) ≫
            (fᵢ.hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d
              a b ≫ fⱼ.inv) =
          G.map (eᵢ.hom ≫ K.d a b ≫ eⱼ.inv) ≫
            (G.map eⱼ.hom ≫ mⱼ.hom ≫ fⱼ.inv)
        calc
          _ = G.map eᵢ.hom ≫
              (mᵢ.hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d
                a b) ≫ fⱼ.inv := by
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
          _ = G.map eᵢ.hom ≫
              (G.map (K.d a b) ≫ mⱼ.hom) ≫ fⱼ.inv := by
            rw [show mᵢ.hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d
                a b = G.map (K.d a b) ≫ mⱼ.hom by
              exact mapXIso_naturality K a b]
          _ = _ := by simp [Functor.map_comp, Category.assoc]
      · exact (((G.mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X
          ComplexShape.embeddingUpNat j (fun k hk ↦ hj ⟨k, hk⟩) |>.eq_of_tgt _ _)
    · exact (G.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i
        (fun k hk ↦ hi ⟨k, hk⟩)) |>.eq_of_src _ _)

lemma mapExtendIso_hom_f (K : CochainComplex C ℕ) (n : ℤ) :
    (mapExtendIso (G := G) K).hom.f n = (mapExtendXIso (G := G) K n).hom :=
  rfl

theorem mapExtendIso_naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    (G.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) ≫
          (mapExtendIso L).hom =
      (mapExtendIso K).hom ≫
        HomologicalComplex.extendMap
          ((G.mapHomologicalComplex (.up ℕ)).map f) ComplexShape.embeddingUpNat := by
  classical
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    mapExtendIso_hom_f (G := G), mapExtendIso_hom_f (G := G),
    Functor.mapHomologicalComplex_map_f]
  by_cases h : ∃ k, ComplexShape.embeddingUpNat.f k = n
  · obtain ⟨k, hk⟩ := h
    have hk' : (k : ℤ) = n := (ComplexShape.embeddingUpNat_f k).symm.trans hk
    clear hk
    subst n
    rw [HomologicalComplex.extendMap_f f ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f k),
      HomologicalComplex.extendMap_f
        ((G.mapHomologicalComplex (.up ℕ)).map f)
        ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)]
    rw [mapExtendXIso_natCast (G := G) K k, mapExtendXIso_natCast (G := G) L k]
    rw [Functor.mapHomologicalComplex_map_f]
    simp only [G.map_comp, Iso.trans_hom, mapXIso]
    let eK := HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
      (ComplexShape.embeddingUpNat_f k)
    let eL := HomologicalComplex.extendXIso L ComplexShape.embeddingUpNat
      (ComplexShape.embeddingUpNat_f k)
    let gK := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
      ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)
    let gL := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj L)
      ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)
    change (G.map eK.hom ≫ G.map (f.f k) ≫ G.map eL.inv) ≫
        (G.map eL.hom ≫ 𝟙 _ ≫ gL.inv) =
      (G.map eK.hom ≫ 𝟙 _ ≫ gK.inv) ≫
        (gK.hom ≫ G.map (f.f k) ≫ gL.inv)
    have heL : G.map eL.inv ≫ G.map eL.hom = 𝟙 _ :=
      (G.mapIso eL).inv_hom_id
    have heLgL : G.map eL.inv ≫ G.map eL.hom ≫ gL.inv = gL.inv :=
      (G.mapIso eL).inv_hom_id_assoc gL.inv
    have hgK : gK.inv ≫ gK.hom ≫ G.map (f.f k) ≫ gL.inv =
        G.map (f.f k) ≫ gL.inv := by
      exact gK.inv_hom_id_assoc (G.map (f.f k) ≫ gL.inv)
    calc
      _ = G.map eK.hom ≫ G.map (f.f k) ≫ gL.inv := by
        have hunit : (𝟙 (G.obj (L.X k))) ≫ gL.inv = gL.inv :=
          Category.id_comp gL.inv
        have htail₀ : G.map eL.hom ≫ 𝟙 _ ≫ gL.inv =
            G.map eL.hom ≫ gL.inv :=
          congrArg (fun q ↦ G.map eL.hom ≫ q) hunit
        have htail : G.map eL.inv ≫
            (G.map eL.hom ≫ 𝟙 _ ≫ gL.inv) = gL.inv :=
          (congrArg (fun q ↦ G.map eL.inv ≫ q) htail₀).trans heLgL
        have houter := Category.assoc
          (G.map eK.hom) (G.map (f.f k) ≫ G.map eL.inv)
          (G.map eL.hom ≫ 𝟙 _ ≫ gL.inv)
        have hinner := Category.assoc (G.map (f.f k)) (G.map eL.inv)
          (G.map eL.hom ≫ 𝟙 _ ≫ gL.inv)
        have hinnerWhisker := congrArg (fun q ↦ G.map eK.hom ≫ q) hinner
        have hcancelWhisker := congrArg
          (fun q ↦ G.map eK.hom ≫ G.map (f.f k) ≫ q) htail
        exact houter.trans (hinnerWhisker.trans hcancelWhisker)
      _ = _ := by
        simp only [Category.assoc]
        apply (cancel_epi (G.mapIso eK).hom).2
        exact hgK.symm
  · exact (((G.mapHomologicalComplex (.up ℕ)).obj L).isZero_extend_X
      ComplexShape.embeddingUpNat n (fun k hk ↦ h ⟨k, hk⟩) |>.eq_of_tgt _ _)

end KltDP.CochainComparison
