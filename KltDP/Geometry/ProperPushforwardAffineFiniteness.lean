import KltDP.Geometry.ProperAffineSectionsFinite
import KltDP.Geometry.PushforwardRelativeGluingData
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Finiteness of the original proper pushforward on affine base charts

The accepted proper-cohomology finiteness producer is applied to the
original restricted proper morphism and the original affine chart
isomorphism. Cancelling only these actual ring isomorphisms proves
finiteness of the literal original section map `f.app U`.

The spectrum map and the component of the actual relative gluing datum
are then finite. The base is an arbitrary locally Noetherian scheme;
no field, integral, reduced, or geometric-fibre assumption is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProperPushforwardAffineFiniteness

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Original affine-chart pushforward sections are finite over the original base sections. -/
theorem app_finite [IsLocallyNoetherian Y] [IsProper f] (U : Y.AffineZariskiSite) :
    (f.app U.1).hom.Finite := by
  letI : IsNoetherianRing Γ(Y, U.1) :=
    IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
  letI : IsProper (f ∣_ U.1) :=
    IsLocalAtTarget.restrict (P := @IsProper) inferInstance U.1
  let g : (f ⁻¹ᵁ U.1).toScheme ⟶ Spec Γ(Y, U.1) := (f ∣_ U.1) ≫ U.2.isoSpec.hom
  letI : IsProper g := inferInstance
  have he : CommRingCat.ofHom (ProperAffineSections.baseScalar g) =
      U.1.topIso.inv ≫ (f ∣_ U.1).appTop := by
    change (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫ g.appTop = _
    rw [Scheme.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h : (CommRingCat.ofHom (ProperAffineSections.baseScalar g)).hom.Finite :=
    ProperAffineSections.baseScalar_finite g
  rw [he, CommRingCat.hom_comp, RingHom.finite_respectsIso.cancel_left_isIso] at h
  rw [morphismRestrict_appTop, CommRingCat.hom_comp,
    RingHom.finite_respectsIso.cancel_right_isIso] at h
  have h : (f.app (U.1.ι ''ᵁ ⊤)).hom.Finite := h
  rwa [Scheme.Opens.ι_image_top] at h

private theorem specMap_isFinite {A B : CommRingCat.{u}} (g : A ⟶ B)
    (hg : g.hom.Finite) : AlgebraicGeometry.IsFinite (Spec.map g) := by
  apply (HasAffineProperty.iff_of_isAffine (P := @AlgebraicGeometry.IsFinite)).mpr
  refine ⟨inferInstance, ?_⟩
  have H := RingHom.finite_respectsIso
  rw [← H.cancel_right_isIso _ (Scheme.ΓSpecIso _).hom,
    ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp,
    H.cancel_left_isIso]
  exact hg

/-- The spectrum of the literal affine-chart section map is finite. -/
theorem spec_map_app_isFinite [IsLocallyNoetherian Y] [IsProper f]
    (U : Y.AffineZariskiSite) : IsFinite (Spec.map (f.app U.1)) :=
  specMap_isFinite (f.app U.1) (app_finite f U)

/-- Each original base component of the actual relative gluing datum is finite. -/
theorem datum_natTrans_isFinite [IsLocallyNoetherian Y] [IsProper f]
    (U : Y.AffineZariskiSite) : IsFinite ((PushforwardRelativeSpec.datum f).natTrans.app U) := by
  letI : IsFinite (Spec.map (f.app U.1)) := spec_map_app_isFinite f U
  change IsFinite (Spec.map (f.app U.1) ≫ U.2.isoSpec.inv)
  infer_instance

end KltDP.Geometry.ProperPushforwardAffineFiniteness
