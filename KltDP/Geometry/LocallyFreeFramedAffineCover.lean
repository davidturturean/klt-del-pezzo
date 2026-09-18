/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Compatibility.AffineZariskiDirectedCover
import KltDP.Geometry.SheafFrameRestriction

/-!
# An original affine directed cover subordinate to actual sheaf frames

The index is the subtype of the original affine Zariski site consisting of
opens contained in some original frame chart. Its arrows are the original
basic-open inclusions. The original affine-site common refinements remain
in this subtype, so the existing directedness proof applies.

Every member has a basis of the original module of sections, obtained by
restricting one eligible original sheaf frame. Different members may choose
different frames. No compatibility of those choices is asserted or assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
universe u
namespace KltDP.Geometry.LocallyFreeFramedAffineCover

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] SheafFrameRestriction.overHasWeakSheafify
  SheafFrameRestriction.overWEqualsLocallyBijective

variable {X : Scheme.{u}} {M : X.Modules} {n : ℕ}
  (t : KltDP.SheafOfModules.ConstantRankTrivializations
    (R := X.ringCatSheaf) M (n + 1))

/-- Original affine opens contained in an original frame chart. -/
abbrev Index := {U : X.AffineZariskiSite // ∃ i : t.I, U.1 ≤ t.X i}

/-- The original local-frame covering is a covering of original points. -/
theorem exists_mem_frame (x : X) : ∃ i : t.I, x ∈ t.X i := by
  obtain ⟨U, f, ⟨i, ⟨g⟩⟩, hxU⟩ := t.coversTop ⊤ x (by trivial)
  exact ⟨i, g.le hxU⟩

/-- The actual eligible affine opens and their original inclusions cover X. -/
def cover : X.OpenCover :=
  Scheme.Cover.mkOfCovers (Index t)
    (fun U => U.1.1.toScheme) (fun U => U.1.1.ι)
    (fun x => by
      obtain ⟨i, hxi⟩ := exists_mem_frame t x
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUi⟩ :=
        (isBasis_affine_open X).exists_subset_of_mem_open hxi (t.X i).2
      exact ⟨⟨⟨U, hU⟩, ⟨i, hUi⟩⟩, ⟨x, hxU⟩, rfl⟩)

instance : Preorder (cover t).J := inferInstanceAs (Preorder (Index t))

instance : SmallCategory (cover t).J := inferInstanceAs (SmallCategory (Index t))

/-- The original affine-site overlap refinement is still eligible because it
lies inside either of the original eligible opens. -/
instance : Scheme.Cover.LocallyDirected (cover t) where
  trans {U V} hij := X.homOfLE (Scheme.AffineZariskiSite.toOpens_mono hij.le)
  trans_id U := Scheme.homOfLE_rfl X U.1.1
  trans_comp hij hjk := (Scheme.homOfLE_homOfLE X _ _).symm
  w hij := Scheme.homOfLE_ι X _
  directed {U V} x := by
    obtain ⟨W, hWU, hWV, y, hy⟩ := Scheme.Cover.exists_lift_trans_eq
      (Scheme.AffineZariskiSite.directedCover X) (i := U.1) (j := V.1) x
    have hW : ∃ i : t.I, W.1 ≤ t.X i := by
      obtain ⟨i, hi⟩ := U.2
      exact ⟨i, (Scheme.AffineZariskiSite.toOpens_mono hWU.le).trans hi⟩
    refine ⟨⟨W, hW⟩, homOfLE hWU.le, homOfLE hWV.le, y, ?_⟩
    exact hy

/-- The diagram of the actual ambient opens and their original inclusions. -/
def toOpensFunctor : Index t ⥤ X.Opens :=
  (show Monotone (fun U : Index t => U.1.1) from
    fun _ _ h => Scheme.AffineZariskiSite.toOpens_mono h).functor

/-- The natural affine comparison retains the original section rings and
restriction homomorphisms on this actual subordinate cover. -/
def restrictIsoSpec :
    Scheme.Cover.functorOfLocallyDirected (cover t) ≅
      toOpensFunctor t ⋙ X.presheaf.rightOp ⋙ Scheme.Spec :=
  NatIso.ofComponents (fun U => U.1.2.isoSpec) (fun {U V} hij =>
    (Scheme.Opens.toSpecΓ_SpecMap_map U.1.1 V.1.1
      (Scheme.AffineZariskiSite.toOpens_mono hij.le)).symm)

/-- Choose one eligible original chart for the given original affine open. -/
def frameIndex (U : Index t) : t.I := U.2.choose

theorem le_frameIndex (U : Index t) : U.1.1 ≤ t.X (frameIndex t U) :=
  U.2.choose_spec

/-- The original module of sections over each eligible affine open has the
basis obtained from its chosen original sheaf presentation. -/
def basis (U : Index t) :
    Basis (Fin (n + 1)) Γ(X, U.1.1) (M.val.obj (op U.1.1)) :=
  SheafFrameRestriction.atlasFrame t (frameIndex t U) U.1.1 (le_frameIndex t U)

end KltDP.Geometry.LocallyFreeFramedAffineCover

#print axioms KltDP.Geometry.LocallyFreeFramedAffineCover.cover
#print axioms KltDP.Geometry.LocallyFreeFramedAffineCover.restrictIsoSpec
#print axioms KltDP.Geometry.LocallyFreeFramedAffineCover.basis
