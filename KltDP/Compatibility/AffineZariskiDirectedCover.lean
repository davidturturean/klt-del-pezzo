/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

Bounded adaptation of Mathlib 80cbd0498ab39e21d24d6730b3f932cec672a702,
AlgebraicGeometry/Sites/SmallAffineZariski.lean:92-96,225-250,260-265.
The original pinned affine site and open-cover/gluing APIs are retained.
The colimit proof transports the original directed-cover cocone through
the actual chart isomorphisms, without the newer relative-gluing machinery.
-/
import KltDP.Compatibility.DirectedOpenCover
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.AffineZariskiSite

/-- The original affine-site charts, with their original inclusions, cover the scheme. -/
def directedCover (X : Scheme.{u}) : OpenCover.{u} X :=
  Cover.mkOfCovers X.AffineZariskiSite (fun U => U.1.toScheme) (fun U => U.1.ι)
    (fun x => by
      have hx : x ∈ ⨆ U : X.affineOpens, U.1 := by rw [iSup_affineOpens_eq_top]; trivial
      obtain ⟨U, hxU⟩ := Opens.mem_iSup.mp hx
      exact ⟨⟨U.1, U.2⟩, ⟨x, hxU⟩, rfl⟩)

instance (X : Scheme.{u}) : Preorder (directedCover X).J :=
  inferInstanceAs (Preorder X.AffineZariskiSite)

instance (X : Scheme.{u}) : SmallCategory (directedCover X).J :=
  inferInstanceAs (SmallCategory X.AffineZariskiSite)

/-- Common basic affine opens give the actual directedness of the original affine site. -/
instance (X : Scheme.{u}) : Cover.LocallyDirected (directedCover X) where
  trans {U V} hij := X.homOfLE (toOpens_mono hij.le)
  trans_id U := Scheme.homOfLE_rfl X U.1
  trans_comp hij hjk := (Scheme.homOfLE_homOfLE X _ _).symm
  w hij := Scheme.homOfLE_ι X _
  directed {U V} x := by
    let a : X := (pullback.fst U.1.ι V.1.ι ≫ U.1.ι).base x
    have haU : a ∈ U.1 := ((pullback.fst U.1.ι V.1.ι).base x).2
    have haV : a ∈ V.1 := by
      change (pullback.fst U.1.ι V.1.ι ≫ U.1.ι).base x ∈ V.1
      rw [pullback.condition]
      exact ((pullback.snd U.1.ι V.1.ι).base x).2
    obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 a ⟨haU, haV⟩
    have hfg : U.basicOpen f = V.basicOpen g := Subtype.ext e
    let y : (U.basicOpen f).1 := ⟨a, hxf⟩
    refine ⟨U.basicOpen f, homOfLE (U.basicOpen_le f),
      eqToHom hfg ≫ homOfLE (V.basicOpen_le g), y, ?_⟩
    apply (show IsOpenImmersion (pullback.fst U.1.ι V.1.ι ≫ U.1.ι) from
      inferInstance).base_open.injective
    change (pullback.lift (W := (U.basicOpen f).1.toScheme)
      (X.homOfLE (toOpens_mono (U.basicOpen_le f)))
      (X.homOfLE (toOpens_mono
        (eqToHom hfg ≫ homOfLE (V.basicOpen_le g)).le))
      (by simp) ≫ pullback.fst U.1.ι V.1.ι ≫ U.1.ι).base y =
        (pullback.fst U.1.ι V.1.ι ≫ U.1.ι).base x
    rw [pullback.lift_fst_assoc, Scheme.homOfLE_ι]
    rfl

/-- The original affine-site diagram is the diagram of spectra of the original sections. -/
def restrictIsoSpec (X : Scheme.{u}) :
    Cover.functorOfLocallyDirected (directedCover X) ≅
      toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ Scheme.Spec :=
  NatIso.ofComponents (fun U => U.2.isoSpec) (fun {U V} hij =>
    (Scheme.Opens.toSpecΓ_SpecMap_map U.1 V.1 (toOpens_mono hij.le)).symm)

/-- The actual affine-spectrum cocone whose point is the original scheme. -/
def cocone (X : Scheme.{u}) : Cocone (toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ Scheme.Spec) :=
  (Cocones.precompose (restrictIsoSpec X).inv).obj
    (Cover.coconeOfLocallyDirected (directedCover X))

/-- Its chart maps are literally the original affine-open maps from spectra. -/
theorem cocone_ι_app (X : Scheme.{u}) (U : X.AffineZariskiSite) :
    (cocone X).ι.app U = U.2.fromSpec := rfl

/-- The original scheme is the colimit of its original affine-spectrum diagram. -/
def isColimitCocone (X : Scheme.{u}) : IsColimit (cocone X) :=
  (IsColimit.precomposeInvEquiv (restrictIsoSpec X)
    (Cover.coconeOfLocallyDirected (directedCover X))).symm
      (Cover.isColimitCoconeOfLocallyDirected (directedCover X))

end AlgebraicGeometry.Scheme.AffineZariskiSite
