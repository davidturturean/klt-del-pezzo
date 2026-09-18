import KltDP.Geometry.PushforwardBasicOpenLocalization
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.VanKampen
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The original pushforward algebra on the affine Zariski site

The rings, restrictions and scalar map are the original structure-sheaf
pushforward. Their spectra form the actual affine diagram for relative
Spec. Distinguished restriction squares are pullbacks by the pinned
localization base-change theorem, with every scalar map retained.

This specializes the localization argument in Mathlib's later
SmallAffineZariski (80cbd0498ab39e21d24d6730b3f932cec672a702, 270-294),
using the pinned `Algebra.isPushout_of_isLocalization` and original Spec
pullback theorem. No newer API or assumed gluing object is required.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u

namespace KltDP.Geometry.PushforwardAffineDiagram

open Scheme.AffineZariskiSite PushforwardBasicOpenLocalization

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The literal original pushforward rings and restrictions on the affine site. -/
def sections : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  (toOpensFunctor Y).op ⋙ (Opens.map f.base).op ⋙ X.presheaf

/-- The actual structure-sheaf map, restricted to the original affine site. -/
def scalarMap : (toOpensFunctor Y).op ⋙ Y.presheaf ⟶ sections f where
  app U := f.app U.unop.1
  naturality {U V} i := f.naturality ((toOpensFunctor Y).op.map i)

/-- The spectra of the actual pushforward rings, with their actual restriction maps. -/
def spectra : Y.AffineZariskiSite ⥤ Scheme.{u} :=
  (sections f).rightOp ⋙ Scheme.Spec

/-- Their canonical map to the spectra of the original affine base opens. -/
def toBaseSpectra : spectra f ⟶ toOpensFunctor Y ⋙ Y.presheaf.rightOp ⋙ Scheme.Spec :=
  whiskerRight (NatTrans.rightOp (scalarMap f)) Scheme.Spec

@[simp] theorem spectra_obj (U : Y.AffineZariskiSite) :
    (spectra f).obj U = Spec Γ(X, f ⁻¹ᵁ U.1) := rfl

@[simp] theorem toBaseSpectra_app (U : Y.AffineZariskiSite) :
    (toBaseSpectra f).app U = Spec.map (f.app U.1) := rfl

/-- Every original distinguished affine restriction square is cartesian. -/
theorem basicOpen_isPullback [QuasiCompact f] [QuasiSeparated f]
    (U : Y.AffineZariskiSite) (r : Γ(Y, U.1)) :
    IsPullback (Spec.map (restriction f U.1 r))
      (Spec.map (f.app (Y.basicOpen r))) (Spec.map (f.app U.1))
      (Spec.map (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op)) := by
  let a := f.app U.1
  let b := Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op
  let c := restriction f U.1 r
  let d := f.app (Y.basicOpen r)
  letI := a.hom.toAlgebra
  letI := b.hom.toAlgebra
  letI := c.hom.toAlgebra
  letI := d.hom.toAlgebra
  letI := (c.hom.comp a.hom).toAlgebra
  letI : IsScalarTower Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)
      Γ(X, f ⁻¹ᵁ Y.basicOpen r) := .of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(Y, U.1) Γ(Y, Y.basicOpen r)
      Γ(X, f ⁻¹ᵁ Y.basicOpen r) := .of_algebraMap_eq' (by
    exact congrArg CommRingCat.Hom.hom (restriction_square f U.1 r).symm)
  letI : IsLocalization.Away r Γ(Y, Y.basicOpen r) := U.2.isLocalization_basicOpen r
  have hloc := isLocalization_preimage_basicOpen f ⟨U.1, U.2⟩ r
  letI : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ U.1) (.powers r))
      Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers,
      RingHom.algebraMap_toAlgebra] using hloc
  letI : Algebra.IsPushout Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)
      Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    Algebra.isPushout_of_isLocalization (.powers r) Γ(Y, Y.basicOpen r)
      Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r)
  exact isPullback_Spec_map_isPushout a b c d
    (CommRingCat.isPushout_of_isPushout Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)
      Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r))

/-- The original spectrum diagram has cartesian squares over every affine-site arrow. -/
theorem toBaseSpectra_equifibered [QuasiCompact f] [QuasiSeparated f] :
    NatTrans.Equifibered (toBaseSpectra f) := by
  intro U V i
  obtain ⟨r, hr⟩ := i.le
  obtain rfl : V.basicOpen r = U := Subtype.ext hr
  exact basicOpen_isPullback f V r

end KltDP.Geometry.PushforwardAffineDiagram
