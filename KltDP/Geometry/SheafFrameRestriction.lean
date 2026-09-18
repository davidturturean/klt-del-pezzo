/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Compatibility.ConstantRankSheaf
import KltDP.Compatibility.FreeSheafTransportedBasis
import KltDP.Geometry.FrameRestrictionDeterminant
import KltDP.Geometry.InvertibleSheaf
import KltDP.Geometry.TransitionUnitSections

/-!
# Actual local sheaf frames on all original subopens

A free presentation of the original module sheaf over an original open gives
bases of its original sections on every smaller open. The original semilinear
restriction carries basis vectors, coordinates and frame-change matrices to
those on the smaller open. In particular, two presentations on different opens
give bases of the very same section module on their full intersection.

The constant-rank atlas is the existing atlas extracted from actual local
bases. No projective chart, localization equivalence or compatibility witness
is assumed here.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Compatibility.FreeSheafTransportedBasis
open KltDP.Geometry.TransitionUnitGluing
universe u
namespace KltDP.Geometry.SheafFrameRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance overHasWeakSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrp.{u} :=
  (CategoryTheory.plusPlusAdjunction
    ((Opens.grothendieckTopology X).over U) AddCommGrp.{u}).isRightAdjoint

local instance overWEqualsLocallyBijective (X : Scheme.{u}) (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrp.{u} := by
  let J := (Opens.grothendieckTopology X).over U
  letI : J.PreservesSheafification (forget AddCommGrp.{u}) :=
    GrothendieckTopology.instPreservesSheafification J (forget AddCommGrp.{u})
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallyInjective_toSheafify' J P
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallySurjective_toSheafify' J P
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' J AddCommGrp.{u}

variable {X : Scheme.{u}} (M : X.Modules) {n : ℕ}

/-- Original section restriction, with its original structure-ring map. -/
def restrict {V W : X.Opens} (h : V ≤ W) :
    M.val.obj (op W) →ₛₗ[res X h] M.val.obj (op V) where
  toFun := M.val.map (homOfLE h).op
  map_add' x y := map_add _ x y
  map_smul' r x := M.val.map_smul (homOfLE h).op r x

variable {M} {U : X.Opens}
  (e : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U)
    (ULift.{u} (Fin n)) ≅ M.over U)

/-- Evaluate the actual sheaf presentation at the original subopen. -/
def frameULift (W : X.Opens) (hW : W ≤ U) :
    Basis (ULift.{u} (Fin n)) Γ(X, W) (M.val.obj (op W)) :=
  transportedBasis (X.ringCatSheaf.over U) (ULift.{u} (Fin n))
    (M.over U) e (op (Over.mk (homOfLE hW)))

/-- The same original basis with the standard finite index. -/
def frame (W : X.Opens) (hW : W ≤ U) :
    Basis (Fin n) Γ(X, W) (M.val.obj (op W)) :=
  (frameULift e W hW).reindex (Equiv.ulift.{u, 0} (α := Fin n))

/-- The original restriction sends every original frame vector to the
corresponding frame vector on the smaller open. -/
theorem frame_restrict {V W : X.Opens} (hVW : V ≤ W) (hW : W ≤ U) (i : Fin n) :
    restrict M hVW (frame e W hW i) = frame e V (hVW.trans hW) i := by
  change restrict M hVW
      ((frameULift e W hW).reindex (Equiv.ulift.{u, 0} (α := Fin n)) i) =
    (frameULift e V (hVW.trans hW)).reindex (Equiv.ulift.{u, 0} (α := Fin n)) i
  rw [Basis.reindex_apply, Basis.reindex_apply]
  exact transportedBasis_map (X.ringCatSheaf.over U) (ULift.{u} (Fin n))
    (M.over U) e
    (Over.homMk (homOfLE hVW) (Subsingleton.elim _ _) :
      Over.mk (homOfLE (hVW.trans hW)) ⟶ Over.mk (homOfLE hW)).op _

/-- Coordinates of every original section restrict by the original ring map. -/
theorem frame_repr_restrict {V W : X.Opens} (hVW : V ≤ W) (hW : W ≤ U)
    (s : M.val.obj (op W)) (i : Fin n) :
    (frame e V (hVW.trans hW)).repr (restrict M hVW s) i =
      res X hVW ((frame e W hW).repr s i) :=
  FrameRestrictionDeterminant.repr_restrict
    (frame e W hW) (frame e V (hVW.trans hW)) (restrict M hVW)
    (frame_restrict e hVW hW) s i

variable {U' : X.Opens}
  (e' : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U')
    (ULift.{u} (Fin n)) ≅ M.over U')

/-- Both frame changes on an overlap are computed in the same original
section module, and their matrices restrict entry by entry. -/
theorem frame_toMatrix_restrict {V W : X.Opens} (hVW : V ≤ W)
    (hW : W ≤ U) (hW' : W ≤ U') :
    (frame e V (hVW.trans hW)).toMatrix (frame e' V (hVW.trans hW')) =
      ((frame e W hW).toMatrix (frame e' W hW')).map (res X hVW) :=
  FrameRestrictionDeterminant.toMatrix_restrict
    (frame e W hW) (frame e' W hW')
    (frame e V (hVW.trans hW)) (frame e' V (hVW.trans hW'))
    (restrict M hVW) (frame_restrict e hVW hW) (frame_restrict e' hVW hW')

/-- Every actual constant-rank atlas therefore supplies original bases on
all overlaps, including opens which need not be affine. -/
def atlasFrame (t : KltDP.SheafOfModules.ConstantRankTrivializations M n)
    (i : t.I) (W : X.Opens) (hW : W ≤ t.X i) :
    Basis (Fin n) Γ(X, W) (M.val.obj (op W)) :=
  frame (t.iso i) W hW

/-- Naturality for the atlas obtained from the original local-basis predicate. -/
theorem atlasFrame_restrict
    (t : KltDP.SheafOfModules.ConstantRankTrivializations M n)
    (i : t.I) {V W : X.Opens} (hVW : V ≤ W) (hW : W ≤ t.X i) (j : Fin n) :
    restrict M hVW (atlasFrame t i W hW j) =
      atlasFrame t i V (hVW.trans hW) j :=
  frame_restrict (t.iso i) hVW hW j

end KltDP.Geometry.SheafFrameRestriction

#print axioms KltDP.Geometry.SheafFrameRestriction.frame
#print axioms KltDP.Geometry.SheafFrameRestriction.frame_repr_restrict
#print axioms KltDP.Geometry.SheafFrameRestriction.frame_toMatrix_restrict
#print axioms KltDP.Geometry.SheafFrameRestriction.atlasFrame_restrict
