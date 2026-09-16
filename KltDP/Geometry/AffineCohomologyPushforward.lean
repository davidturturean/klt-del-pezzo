/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

The localization argument follows official Mathlib Tilde.lean:543-571 at
79d0395a1825a6264ad5d269e35e60537518955e. The affine-isomorphism assembly
follows Vasily Ilin's SchemeModuleCohomologyAffineCover.lean:105-137 at
Vilin97/MazurTheorem 9327963d4ec14fba49c7b14b004fd00707ffc2e9 (Apache 2.0).
This port uses the actual pinned section objects and the project's proved
denominator-extension criterion instead of the modern IsLocalizing API.
-/
import KltDP.Geometry.AffineCohomologyIsoTransport
import KltDP.Geometry.AffineQuasicoherentKernels
import KltDP.Geometry.SchemeModulePushforwardScalars

/-!
# Quasicoherence of affine pushforward

For Spec(S) to Spec(R), the preimage of D(r) is D(phi(r)). The original
pushforward has the same section groups, with exactly the phi-restricted
scalar action. Both denominator properties therefore transfer from S to R.
The existing original counit criterion gives quasicoherence. The final
assembly applies to every morphism of actual affine schemes.

Source draft; VM elaboration and compiled dependency audit remain pending.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineCohomologyPort

open AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
  (M : (Spec (.of S)).Modules)

/-- Pushforward retains the actual section group on the actual preimage open. -/
def specPushforwardSectionsAddEquiv (U : (Spec (.of R)).Opens) :
    sectionModule ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj M) U ≃+
      sectionModule M (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U) :=
  AddEquiv.refl _

/-- Its R-action is precisely the original S-action through phi. -/
theorem specPushforwardSectionsAddEquiv_smul (U : (Spec (.of R)).Opens) (r : R)
    (s : sectionModule ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj M) U) :
    specPushforwardSectionsAddEquiv φ M U (r • s) =
      φ r • specPushforwardSectionsAddEquiv φ M U s := by
  let f := Spec.map (CommRingCat.ofHom φ)
  let act : (Spec (.of S)).ringCatSheaf.val.obj (op (f ⁻¹ᵁ U)) →
      M.val.obj (op (f ⁻¹ᵁ U)) → M.val.obj (op (f ⁻¹ᵁ U)) :=
    @SMul.smul _ _ (M.val.obj (op (f ⁻¹ᵁ U))).isModule.toSMul
  change act (f.app U ((Spec (.of R)).presheaf.map
      (homOfLE (show U ≤ ⊤ from le_top)).op ((Scheme.ΓSpecIso (.of R)).inv r))) s =
    act ((Spec (.of S)).presheaf.map
      (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        ((Scheme.ΓSpecIso (.of S)).inv (φ r))) s
  rw [ModuleCohomology.app_restrictGlobal]
  have hr : f.appTop ((Scheme.ΓSpecIso (.of R)).inv r) =
      (Scheme.ΓSpecIso (.of S)).inv (φ r) :=
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)) r).symm
  rw [hr]

/-- Replace the preimage open by an equal actual open. -/
def specPushforwardSectionsAddEquivOfEq (U : (Spec (.of R)).Opens)
    (V : (Spec (.of S)).Opens) (h : Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U = V) :
    sectionModule ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj M) U ≃+
      sectionModule M V := by
  subst V
  exact specPushforwardSectionsAddEquiv φ M U

/-- The equal-open comparison retains the same original scalar action. -/
theorem specPushforwardSectionsAddEquivOfEq_smul (U : (Spec (.of R)).Opens)
    (V : (Spec (.of S)).Opens) (h : Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U = V) (r : R)
    (s : sectionModule ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj M) U) :
    specPushforwardSectionsAddEquivOfEq φ M U V h (r • s) =
      φ r • specPushforwardSectionsAddEquivOfEq φ M U V h s := by
  subst V
  exact specPushforwardSectionsAddEquiv_smul φ M U r s

/-- The comparisons commute with original restriction maps. -/
theorem specPushforwardSectionsAddEquivOfEq_naturality
    {U V : (Spec (.of R)).Opens} {U' V' : (Spec (.of S)).Opens}
    (hU : Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U = U')
    (hV : Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ V = V') (h : V ≤ U) (h' : V' ≤ U')
    (s : sectionModule ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj M) U) :
    specPushforwardSectionsAddEquivOfEq φ M V V' hV
        (sectionRestrict ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj M) h s) =
      sectionRestrict M h' (specPushforwardSectionsAddEquivOfEq φ M U U' hU s) := by
  subst U'
  subst V'
  rfl

/-- Both denominator properties transfer along the actual affine structure map. -/
theorem specPushforward_denominatorExtension
    (hM : DenominatorExtension M ⊤) :
    DenominatorExtension ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj M) ⊤ := by
  let P := (schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj M
  have htop : Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens) = ⊤ := rfl
  have hbasic (r : R) : Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ PrimeSpectrum.basicOpen r =
      PrimeSpectrum.basicOpen (φ r) := PrimeSpectrum.comap_basicOpen φ r
  let eTop := specPushforwardSectionsAddEquivOfEq φ M ⊤ ⊤ htop
  let e (r : R) := specPushforwardSectionsAddEquivOfEq φ M
    (PrimeSpectrum.basicOpen r) (PrimeSpectrum.basicOpen (φ r)) (hbasic r)
  have natural (r : R) (t : sectionModule P ⊤) :
      e r (sectionRestrict P le_top t) = sectionRestrict M le_top (eTop t) :=
    specPushforwardSectionsAddEquivOfEq_naturality φ M htop (hbasic r) le_top le_top t
  have scalarTop (r : R) (t : sectionModule P ⊤) : eTop (r • t) = φ r • eTop t :=
    specPushforwardSectionsAddEquivOfEq_smul φ M ⊤ ⊤ htop r t
  have scalar (f r : R) (s : sectionModule P (PrimeSpectrum.basicOpen f)) :
      e f (r • s) = φ r • e f s :=
    specPushforwardSectionsAddEquivOfEq_smul φ M (PrimeSpectrum.basicOpen f)
      (PrimeSpectrum.basicOpen (φ f)) (hbasic f) r s
  refine ⟨?_, ?_⟩
  · intro r hr s
    obtain ⟨n, t, ht⟩ := hM.existence (φ r) le_top (e r s)
    refine ⟨n, eTop.symm t, ?_⟩
    apply (e r).injective
    calc
      e r (sectionRestrict P hr (eTop.symm t)) =
          sectionRestrict M le_top (eTop (eTop.symm t)) := natural r _
      _ = (φ r) ^ n • e r s := by rw [AddEquiv.apply_symm_apply]; exact ht
      _ = e r (r ^ n • s) := by
        simpa only [map_pow] using (scalar r (r ^ n) s).symm
  · intro r hr t ht
    have hzero : sectionRestrict M (le_top : PrimeSpectrum.basicOpen (φ r) ≤ ⊤)
        (eTop t) = 0 := by
      rw [← natural, ht, map_zero]
    obtain ⟨n, hn⟩ := hM.uniqueness (φ r) le_top (eTop t) hzero
    refine ⟨n, ?_⟩
    apply eTop.injective
    rw [map_zero]
    calc
      eTop (r ^ n • t) = (φ r) ^ n • eTop t := by
        simpa only [map_pow] using scalarTop (r ^ n) t
      _ = 0 := hn

/-- Pushforward along every map of affine spectra preserves original quasicoherence. -/
theorem pushforward_spec_isQuasicoherent [M.IsQuasicoherent] :
    ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj M).IsQuasicoherent := by
  let P := (schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj M
  letI : IsIso (counit P) := counit_isIso_of_denominatorExtension P
    (specPushforward_denominatorExtension φ M (denominatorExtension_of_isQuasicoherent M))
  letI := tilde_isQuasicoherent ((globalSectionsFunctor R).obj P)
  exact _root_.SheafOfModules.isQuasicoherent_of_isIso
    (R := (Spec (.of R)).ringCatSheaf)
    (M := ((globalSectionsFunctor R).obj P).tilde) (N := P) (counit P)

/-- Pushforward between arbitrary actual affine schemes preserves quasicoherence. -/
theorem pushforward_isQuasicoherent_of_affine {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((schemeModulePushforward f).obj M).IsQuasicoherent := by
  have hf : (X.isoSpec.hom ≫ Spec.map f.appTop) ≫ Y.isoSpec.inv = f := by
    rw [Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let N := (schemeModulePushforward X.isoSpec.hom).obj M
  letI : N.IsQuasicoherent := pushforward_isQuasicoherent_of_iso X.isoSpec M
  let P := (schemeModulePushforward (Spec.map f.appTop)).obj N
  letI : P.IsQuasicoherent := pushforward_spec_isQuasicoherent f.appTop.hom N
  letI : ((schemeModulePushforward Y.isoSpec.inv).obj P).IsQuasicoherent :=
    pushforward_isQuasicoherent_of_iso Y.isoSpec.symm P
  let e :
      (schemeModulePushforward X.isoSpec.hom ⋙
        schemeModulePushforward (Spec.map f.appTop) ⋙
        schemeModulePushforward Y.isoSpec.inv).obj M ≅
        (schemeModulePushforward f).obj M :=
    (isoWhiskerLeft (schemeModulePushforward X.isoSpec.hom)
        (schemeModulePushforwardCompIso (Spec.map f.appTop) Y.isoSpec.inv) ≪≫
      schemeModulePushforwardCompIso X.isoSpec.hom
        (Spec.map f.appTop ≫ Y.isoSpec.inv) ≪≫
      eqToIso (congrArg schemeModulePushforward
        (by simpa only [Category.assoc] using hf))).app M
  exact _root_.SheafOfModules.isQuasicoherent_of_isIso
    (R := Y.ringCatSheaf) (M := (schemeModulePushforward Y.isoSpec.inv).obj P)
    (N := (schemeModulePushforward f).obj M) e.hom

end KltDP.Geometry.AffineCohomologyPort
