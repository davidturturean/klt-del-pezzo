/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.LocallyFreeFramedAffineCover
import KltDP.Geometry.SymmetricProjFramedCoefficient
import KltDP.Compatibility.RelativeGluingData

/-!
# The actual affine symmetric-Proj diagram of a locally free sheaf

Objects are the symmetric Proj schemes of the original affine section modules.
Maps use the original section restrictions in a frame on the larger open,
restricted to the smaller open. Frame independence and composition are proved
from those same actual semilinear restrictions; no transition diagram is assumed.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
namespace KltDP.Geometry.LocallyFreeProjectivization
open LocallyFreeFramedAffineCover RelativeSymmetricProj TransitionUnitGluing
attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] SheafFrameRestriction.overHasWeakSheafify
  SheafFrameRestriction.overWEqualsLocallyBijective

variable {X : Scheme.{u}} {M : X.Modules} {n : ℕ}
  (t : KltDP.SheafOfModules.ConstantRankTrivializations
    (R := X.ringCatSheaf) M (n + 1))

/-- The underlying original inclusion of two members of the affine frame cover. -/
def opensLE {U V : Index t} (h : U ⟶ V) : U.1.1 ≤ V.1.1 :=
  Scheme.AffineZariskiSite.toOpens_mono h.le

/-- The original larger-open frame evaluated on the original smaller open. -/
def restrictedBasis {U V : Index t} (h : U ⟶ V) :
    Basis (Fin (n + 1)) Γ(X, U.1.1) (M.val.obj (op U.1.1)) :=
  SheafFrameRestriction.atlasFrame t (frameIndex t V) U.1.1
    ((opensLE t h).trans (le_frameIndex t V))

/-- The actual symmetric Proj of the original module of affine sections. -/
def piece (U : Index t) : Scheme.{u} :=
  RelativeSymmetricProj.scheme Γ(X, U.1.1) (M.val.obj (op U.1.1))

/-- Restriction is contravariant on the original section rings and covariant
on their actual symmetric Proj schemes. -/
def pieceMap {U V : Index t} (h : U ⟶ V) : piece t U ⟶ piece t V :=
  framedCoefficientMorphism (basis t V) (restrictedBasis t h) (res X (opensLE t h))

/-- Any original frame on the larger open gives this same original scheme map. -/
theorem pieceMap_eq_frame {U V : Index t} (h : U ⟶ V)
    (i : t.I) (hi : V.1.1 ≤ t.X i) :
    pieceMap t h = framedCoefficientMorphism
      (SheafFrameRestriction.atlasFrame t i V.1.1 hi)
      (SheafFrameRestriction.atlasFrame t i U.1.1 ((opensLE t h).trans hi))
      (res X (opensLE t h)) := by
  apply framedCoefficientMorphism_eq_of_preservesFrames
    (basis t V) (SheafFrameRestriction.atlasFrame t i V.1.1 hi)
    (restrictedBasis t h)
    (SheafFrameRestriction.atlasFrame t i U.1.1 ((opensLE t h).trans hi))
    (SheafFrameRestriction.restrict M (opensLE t h))
  · intro j
    exact SheafFrameRestriction.atlasFrame_restrict t (frameIndex t V)
      (opensLE t h) (le_frameIndex t V) j
  · intro j
    exact SheafFrameRestriction.atlasFrame_restrict t i (opensLE t h) hi j

@[simp] theorem pieceMap_id (U : Index t) : pieceMap t (𝟙 U) = 𝟙 (piece t U) := by
  change framedCoefficientMorphism (basis t U) (basis t U)
    (res X (le_refl U.1.1)) = _
  have hr : res X (le_refl U.1.1) = RingHom.id Γ(X, U.1.1) := by
    apply RingHom.ext
    intro a
    exact res_self X U.1.1 a
  rw [hr, framedCoefficientMorphism_id]
  rfl

/-- Original restrictions compose even when the chosen larger-open frames differ. -/
theorem pieceMap_comp {U V W : Index t} (hUV : U ⟶ V) (hVW : V ⟶ W) :
    pieceMap t hUV ≫ pieceMap t hVW = pieceMap t (hUV ≫ hVW) := by
  rw [pieceMap_eq_frame t hUV (frameIndex t W)
    ((opensLE t hVW).trans (le_frameIndex t W))]
  change framedCoefficientMorphism (restrictedBasis t hVW)
      (restrictedBasis t (hUV ≫ hVW)) (res X (opensLE t hUV)) ≫
    framedCoefficientMorphism (basis t W) (restrictedBasis t hVW)
      (res X (opensLE t hVW)) =
    framedCoefficientMorphism (basis t W) (restrictedBasis t (hUV ≫ hVW))
      (res X (opensLE t (hUV ≫ hVW)))
  rw [framedCoefficientMorphism_comp]
  apply congrArg (framedCoefficientMorphism (basis t W) (restrictedBasis t (hUV ≫ hVW)))
  apply RingHom.ext
  intro a
  exact res_res X (opensLE t hUV) (opensLE t hVW) a

/-- The actual affine symmetric-Proj diagram, with its proved functor laws. -/
def diagram : Index t ⥤ Scheme.{u} where
  obj := piece t
  map := pieceMap t
  map_id := pieceMap_id t
  map_comp hUV hVW := (pieceMap_comp t hUV hVW).symm

/-- Original degree-zero maps to the spectra of the original affine section rings. -/
def toBaseSpectra : diagram t ⟶
    toOpensFunctor t ⋙ X.presheaf.rightOp ⋙ Scheme.Spec where
  app U := RelativeSymmetricProj.toBase Γ(X, U.1.1) (M.val.obj (op U.1.1))
  naturality {U V} h :=
    framedCoefficientMorphism_toBase (basis t V) (restrictedBasis t h) (res X (opensLE t h))

/-- Each actual restriction square is cartesian by the original coefficient square. -/
theorem toBaseSpectra_equifibered : NatTrans.Equifibered (toBaseSpectra t) := by
  intro U V h
  exact isPullback_framedCoefficientMorphism (basis t V) (restrictedBasis t h)
    (res X (opensLE t h))

/-- Genuine relative gluing data over the original subordinate affine cover. -/
def datum : Scheme.Cover.RelativeGluingData (cover t) where
  functor := diagram t
  natTrans := toBaseSpectra t ≫ (restrictIsoSpec t).inv
  equifibered := (toBaseSpectra_equifibered t).comp
    (NatTrans.equifibered_of_isIso (restrictIsoSpec t).inv)

end KltDP.Geometry.LocallyFreeProjectivization

#print axioms KltDP.Geometry.LocallyFreeProjectivization.pieceMap_comp
#print axioms KltDP.Geometry.LocallyFreeProjectivization.datum
