/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

Bounded adaptation of the original integral-closure diagram in Mathlib
80cbd0498ab39e21d24d6730b3f932cec672a702, Normalization.lean:45-75.
The original pinned restriction maps and structure sheaf are retained.
-/
import KltDP.Geometry.PushforwardAffineIntegralClosure

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u

namespace KltDP.Geometry.PushforwardIntegralClosureDiagram

open Scheme.AffineZariskiSite
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual integral-closure presheaf inside the original pushforward rings. -/
def diagram : Y.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U :=
    letI := (f.app U.unop).hom.toAlgebra
    CommRingCat.of (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop))
  map {V U} i :=
    CommRingCat.ofHom ((X.presheaf.map (homOfLE (f.preimage_le_preimage_of_le i.unop.le)).op).hom.restrict
      _ _ fun x hx => by
      obtain ⟨U, rfl⟩ := Opposite.op_surjective U
      obtain ⟨V, rfl⟩ := Opposite.op_surjective V
      algebraize [(f.app U).hom, (f.app V).hom, (Y.presheaf.map i).hom,
        (X.presheaf.map (homOfLE (f.preimage_le_preimage_of_le i.unop.le)).op).hom,
        (f.appLE V (f ⁻¹ᵁ U) (f.preimage_le_preimage_of_le i.unop.le)).hom]
      haveI : IsScalarTower Γ(Y, V) Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
        .of_algebraMap_eq' (by
          simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]
          exact congrArg CommRingCat.Hom.hom (f.naturality i).symm)
      haveI : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ U) :=
        .of_algebraMap_eq' rfl
      exact (hx.map (IsScalarTower.toAlgHom Γ(Y, V) _ Γ(X, f ⁻¹ᵁ U))).tower_top)
  map_id U := by simp; rfl
  map_comp i j := by
    simp only [← CommRingCat.ofHom_comp]
    rw [← homOfLE_comp (f.preimage_le_preimage_of_le j.unop.le)
      (f.preimage_le_preimage_of_le i.unop.le), op_comp]
    simp only [X.presheaf.map_comp]
    rfl

/-- The original scalar maps land in the original integral closure. -/
def scalarMap : Y.presheaf ⟶ diagram f where
  app U :=
    letI := (f.app U.unop).hom.toAlgebra
    CommRingCat.ofHom (algebraMap Γ(Y, U.unop)
      (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop)))
  naturality {U V} i := by
    ext x
    exact Subtype.ext (congrArg (fun g : Γ(Y, U.unop) ⟶ Γ(X, f ⁻¹ᵁ V.unop) => g x)
      (f.naturality i))

/-- Inclusion is literally the original integral element viewed as a section. -/
def inclusion : diagram f ⟶ (Opens.map f.base).op ⋙ X.presheaf where
  app U :=
    letI := (f.app U.unop).hom.toAlgebra
    CommRingCat.ofHom (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop)).val.toRingHom
  naturality {U V} i := by ext x; rfl

/-- The actual two scalar maps recover the original structure-sheaf map. -/
theorem scalarMap_inclusion : scalarMap f ≫ inclusion f = f.c := by
  ext U x
  rfl

/-- The original integral closure on the original affine Zariski site. -/
def affineDiagram : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  (toOpensFunctor Y).op ⋙ diagram f

/-- Its canonical inclusion into the actual affine-site pushforward algebra. -/
def affineInclusion : affineDiagram f ⟶ PushforwardAffineDiagram.sections f :=
  whiskerLeft (toOpensFunctor Y).op (inclusion f)

/-- Every original affine component of this inclusion is an isomorphism. -/
instance affineInclusion_app_isIso [UniversallyClosed f]
    (U : Y.AffineZariskiSiteᵒᵖ) : IsIso ((affineInclusion f).app U) := by
  letI := (f.app U.unop.1).hom.toAlgebra
  change IsIso (PushforwardAffineIntegralClosure.closureEquiv f U.unop).toRingEquiv.toCommRingCatIso.hom
  infer_instance

/-- The literal inclusion identifies the original integral-closure diagram with
all original pushforward sections on the affine site. -/
instance affineInclusion_isIso [UniversallyClosed f] : IsIso (affineInclusion f) := by
  apply NatIso.isIso_of_isIso_app

end KltDP.Geometry.PushforwardIntegralClosureDiagram
