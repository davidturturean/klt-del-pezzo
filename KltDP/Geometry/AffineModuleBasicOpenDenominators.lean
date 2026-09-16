/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

Adapted from official Mathlib Tilde.lean:806–842 at
79d0395a1825a6264ad5d269e35e60537518955e, using the project's original
module restriction and the pinned localization-open immersion.
-/
import KltDP.Geometry.AffineModuleRestrictionScalars
import KltDP.Geometry.AffinePresentationDenominators

/-!
# Denominator transport from Spec(R_g) to the original D(g)

The localization's actual scheme map identifies its whole source with
D(g), and identifies D(f/1) with D(f) whenever D(f) is contained in D(g).
The original restriction-section equivalences transport both extension
and zero detection, with the canonical scalar actions. An actual
presentation on the localized scheme therefore gives denominator
extension on the original basic open, without an assumed counit isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTilde

open SchemeModuleRestriction

variable {R : Type u} [CommRing R]

/-- The original localization map has precisely the expected image open. -/
theorem awayRestriction_opensRange (g : R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))).opensRange =
      PrimeSpectrum.basicOpen g :=
  Opens.ext (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g)

/-- The whole localized affine scheme maps to the original D(g). -/
theorem awayRestriction_image_top (g : R) :
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))) ''ᵁ ⊤ =
      PrimeSpectrum.basicOpen g :=
  (Scheme.Hom.image_top_eq_opensRange _).trans (awayRestriction_opensRange g)

/-- The original basic-open pullback is the basic open of the original localized scalar. -/
theorem awayRestriction_preimage_basicOpen (g f : R) :
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))) ⁻¹ᵁ
        PrimeSpectrum.basicOpen f =
      PrimeSpectrum.basicOpen (algebraMap R (Localization.Away g) f) :=
  PrimeSpectrum.comap_basicOpen (algebraMap R (Localization.Away g)) f

/-- A contained basic open is exactly the image of its original localized basic open. -/
theorem awayRestriction_image_basicOpen (g f : R)
    (hf : PrimeSpectrum.basicOpen f ≤ PrimeSpectrum.basicOpen g) :
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))) ''ᵁ
        PrimeSpectrum.basicOpen (algebraMap R (Localization.Away g) f) =
      PrimeSpectrum.basicOpen f := by
  rw [← awayRestriction_preimage_basicOpen,
    Scheme.Hom.image_preimage_eq_opensRange_inter, awayRestriction_opensRange,
    inf_eq_right.mpr hf]

variable (M : (Spec (.of R)).Modules)

/-- Both denominator properties descend along the actual localization-open identification. -/
theorem denominatorExtension_basicOpen_of_away (g : R)
    (h : DenominatorExtension
      ((restriction (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away g))))).obj M) ⊤) :
    DenominatorExtension M (PrimeSpectrum.basicOpen g) := by
  let φ : R →+* Localization.Away g := algebraMap R (Localization.Away g)
  let N := (restriction (Spec.map (CommRingCat.ofHom φ))).obj M
  let eTop := restrictionSectionsAddEquivOfEq φ M ⊤
    (PrimeSpectrum.basicOpen g) (awayRestriction_image_top g)
  let e (f : R) (hf : PrimeSpectrum.basicOpen f ≤ PrimeSpectrum.basicOpen g) :=
    restrictionSectionsAddEquivOfEq φ M (PrimeSpectrum.basicOpen (φ f))
      (PrimeSpectrum.basicOpen f) (awayRestriction_image_basicOpen g f hf)
  have natural (f : R) (hf : PrimeSpectrum.basicOpen f ≤ PrimeSpectrum.basicOpen g)
      (t : sectionModule N ⊤) :
      e f hf (sectionRestrict N le_top t) = sectionRestrict M hf (eTop t) :=
    restrictionSectionsAddEquivOfEq_naturality φ M
      (awayRestriction_image_top g) (awayRestriction_image_basicOpen g f hf) le_top hf t
  have scalarTop (r : R) (t : sectionModule N ⊤) :
      eTop (φ r • t) = r • eTop t :=
    restrictionSectionsAddEquivOfEq_smul φ M ⊤
      (PrimeSpectrum.basicOpen g) (awayRestriction_image_top g) r t
  have scalar (f : R) (hf : PrimeSpectrum.basicOpen f ≤ PrimeSpectrum.basicOpen g)
      (r : R) (s : sectionModule N (PrimeSpectrum.basicOpen (φ f))) :
      e f hf (φ r • s) = r • e f hf s :=
    restrictionSectionsAddEquivOfEq_smul φ M (PrimeSpectrum.basicOpen (φ f))
      (PrimeSpectrum.basicOpen f) (awayRestriction_image_basicOpen g f hf) r s
  refine ⟨?_, ?_⟩
  · intro f hf s
    obtain ⟨n, t, ht⟩ := h.existence (φ f) le_top ((e f hf).symm s)
    refine ⟨n, eTop t, ?_⟩
    calc
      sectionRestrict M hf (eTop t) = e f hf (sectionRestrict N le_top t) :=
        (natural f hf t).symm
      _ = e f hf ((φ f) ^ n • (e f hf).symm s) := congrArg (e f hf) ht
      _ = f ^ n • e f hf ((e f hf).symm s) := by
        simpa only [map_pow] using scalar f hf (f ^ n) ((e f hf).symm s)
      _ = f ^ n • s := by rw [AddEquiv.apply_symm_apply]
  · intro f hf t ht
    have hzero : sectionRestrict N (le_top : PrimeSpectrum.basicOpen (φ f) ≤ ⊤)
        (eTop.symm t) = 0 := by
      apply (e f hf).injective
      rw [map_zero, natural, AddEquiv.apply_symm_apply, ht]
    obtain ⟨n, hn⟩ := h.uniqueness (φ f) le_top (eTop.symm t) hzero
    refine ⟨n, ?_⟩
    calc
      f ^ n • t = f ^ n • eTop (eTop.symm t) := by
        rw [AddEquiv.apply_symm_apply]
      _ = eTop ((φ f) ^ n • eTop.symm t) := by
        simpa only [map_pow] using (scalarTop (f ^ n) (eTop.symm t)).symm
      _ = 0 := by rw [hn, map_zero]

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- An actual presentation on Spec(R_g) yields denominator extension on D(g). -/
theorem denominatorExtension_basicOpen_of_awayPresentation (g : R)
    (P : ((restriction (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away g))))).obj M).Presentation) :
    DenominatorExtension M (PrimeSpectrum.basicOpen g) :=
  denominatorExtension_basicOpen_of_away M g (denominatorExtension_of_presentation _ P)

end KltDP.Geometry.AffineModuleTilde
