/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

The point, structure-sheaf, stalk, and affine-chart constructions below adapt
mathlib PR 26061, ProjectiveSpace.lean, immutable revision
4772397bdbdfdb0cf8050687876c4410a9bc696c, to mathlib
c44e0c8ee63ca166450922a373c7409c5d26b00b. They are specialized to an ordinary
ring equivalence preserving each original homogeneous component in both
directions. The published source is Apache 2.0. KltDP adaptations: 2026.
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Proj transport along a degree-preserving ring equivalence

This source draft constructs maps on the original homogeneous prime ideals,
the original homogeneous localizations, and the original Proj structure sheaf.
The inverse maps and the equation with `Proj.toSpecZero` are proved from those
constructions. The input is a ring equivalence and degree-membership equivalence;
no scheme isomorphism or projectivity witness is an input.

The generic over-base equation allows the original coefficient maps to be
supplied explicitly. No finiteness or nonempty-Proj assumption is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open HomogeneousLocalization

universe u v

namespace KltDP.GradedProjIso

variable {R : Type v} {A B : Type u}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R B}
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- The only compatibility input: the original homogeneous pieces match. -/
def PreservesDegrees (e : A ≃+* B) : Prop :=
  ∀ n x, x ∈ 𝒜 n ↔ e x ∈ ℬ n

variable (e : A ≃+* B) (he : PreservesDegrees (𝒜 := 𝒜) (ℬ := ℬ) e)

include he in
theorem preservesDegrees_symm :
    PreservesDegrees (𝒜 := ℬ) (ℬ := 𝒜) e.symm := by
  intro n x
  simpa only [RingEquiv.apply_symm_apply] using (he n (e.symm x)).symm

def degreeAddHom (n : ℕ) : 𝒜 n →+ ℬ n where
  toFun x := ⟨e x, (he n x).mp x.2⟩
  map_zero' := by ext; exact map_zero e
  map_add' x y := by ext; exact map_add e (x : A) (y : A)

theorem decompose_map (x : A) :
    DirectSum.decompose ℬ (e x) =
      DirectSum.map (degreeAddHom e he) (DirectSum.decompose 𝒜 x) := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x, map_sum, DirectSum.decompose_sum,
    DirectSum.decompose_sum, map_sum]
  congr 1
  ext n : 1
  rw [DirectSum.decompose_of_mem _ ((he _ _).mp (Subtype.prop _)),
    DirectSum.decompose_of_mem _ (Subtype.prop _), DirectSum.map_of]
  rfl

include he in
theorem map_coe_decompose (x : A) (n : ℕ) :
    e (DirectSum.decompose 𝒜 x n) = DirectSum.decompose ℬ (e x) n := by
  rw [decompose_map e he, DirectSum.map_apply]
  rfl

def comapIdeal (I : HomogeneousIdeal ℬ) : HomogeneousIdeal 𝒜 where
  __ := I.toIdeal.comap e.toRingHom
  is_homogeneous' n a ha := by
    change e (DirectSum.decompose 𝒜 a n) ∈ I
    rw [map_coe_decompose e he]
    exact I.is_homogeneous' n ha

def comapPoint (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := comapIdeal e he p.asHomogeneousIdeal
  isPrime := p.isPrime.comap e.toRingHom
  not_irrelevant_le h := by
    apply p.not_irrelevant_le
    intro b hb
    have ha : e.symm b ∈ HomogeneousIdeal.irrelevant 𝒜 := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hb ⊢
      apply e.injective
      rw [map_coe_decompose e he, RingEquiv.apply_symm_apply, hb, map_zero]
    have hb' : e (e.symm b) ∈ p.asHomogeneousIdeal := h ha
    simpa only [RingEquiv.apply_symm_apply] using hb'

@[simp] theorem mem_comapPoint (p : ProjectiveSpectrum ℬ) (a : A) :
    a ∈ (comapPoint e he p).asHomogeneousIdeal ↔ e a ∈ p.asHomogeneousIdeal :=
  Iff.rfl

def comap : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := comapPoint e he
  continuous_toFun := by
    simp only [continuous_iff_isClosed, ProjectiveSpectrum.isClosed_iff_zeroLocus]
    rintro _ ⟨s, rfl⟩
    refine ⟨e '' s, ?_⟩
    ext p
    change (s ⊆ (comapPoint e he p).asHomogeneousIdeal) ↔
      e '' s ⊆ p.asHomogeneousIdeal
    constructor
    · intro hp b hb
      rcases hb with ⟨a, ha, rfl⟩
      have hmem := hp ha
      change e a ∈ p.asHomogeneousIdeal at hmem
      exact hmem
    · intro hp a ha
      change e a ∈ p.asHomogeneousIdeal
      exact hp ⟨a, ha, rfl⟩

def localMap (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
    (hIJ : I = J.comap e.toRingHom) : AtPrime 𝒜 I →+* AtPrime ℬ J :=
  HomogeneousLocalization.map 𝒜 ℬ e.toRingHom
    (Localization.le_comap_primeCompl_iff.mpr (hIJ ▸ le_rfl))
    (fun n a ha ↦ (he n a).mp ha)

@[simp] theorem val_localMap (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
    (hIJ : I = J.comap e.toRingHom) (x : AtPrime 𝒜 I) :
    (localMap e he I J hIJ x).val =
      Localization.localRingHom I J e.toRingHom hIJ x.val := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
  simp only [localMap, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    Localization.localRingHom, Localization.mk_eq_mk', IsLocalization.map_mk']

instance localMap_isLocalHom (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
    (hIJ : I = J.comap e.toRingHom) : IsLocalHom (localMap e he I J hIJ) where
  map_nonunit x hx := by
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val] at hx ⊢
    rw [val_localMap] at hx
    exact IsLocalHom.map_nonunit _ hx

def mapFraction {P : Submonoid A} {Q : Submonoid B}
    (hPQ : P ≤ Q.comap e.toRingHom) (c : NumDenSameDeg 𝒜 P) :
    NumDenSameDeg ℬ Q :=
  ⟨c.deg, degreeAddHom e he _ c.num, degreeAddHom e he _ c.den, hPQ c.den_mem⟩

/-- The localization map sends the displayed original fraction to its displayed image. -/
theorem localMap_mk (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
    (hIJ : I = J.comap e.toRingHom) (c : NumDenSameDeg 𝒜 I.primeCompl) :
    localMap e he I J hIJ (HomogeneousLocalization.mk c) =
      HomogeneousLocalization.mk (mapFraction e he
        (Localization.le_comap_primeCompl_iff.mpr (hIJ ▸ le_rfl)) c) := rfl

section Sections

variable (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))

def sectionMapFun (hUV : V.1 ⊆ comap e he ⁻¹' U.1)
    (s : ∀ x : U, AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) (y : V) :
    AtPrime ℬ y.1.asHomogeneousIdeal.toIdeal :=
  localMap e he _ _ rfl (s ⟨comap e he y.1, hUV y.2⟩)

/-- Transport of one original fraction, before passing to locally fractional sections. -/
theorem isFraction_sectionMapFun
    (hUV : V.1 ⊆ comap e he ⁻¹' U.1)
    (s : ∀ x : U, AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)
    (hs : AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.IsFraction (𝒜 := 𝒜) s) :
    AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.IsFraction (𝒜 := ℬ)
      (sectionMapFun e he U V hUV s) := by
  rcases hs with ⟨n, a, b, hb, h_frac⟩
  have hb' (y : V) : (degreeAddHom e he n b : B) ∉ y.1.asHomogeneousIdeal :=
    hb ⟨comap e he y.1, hUV y.2⟩
  refine ⟨n, degreeAddHom e he n a, degreeAddHom e he n b, hb', ?_⟩
  intro y
  change localMap e he (comapPoint e he y.1).asHomogeneousIdeal.toIdeal
      y.1.asHomogeneousIdeal.toIdeal rfl (s ⟨comap e he y.1, hUV y.2⟩) =
    HomogeneousLocalization.mk ⟨n, degreeAddHom e he n a, degreeAddHom e he n b, hb' y⟩
  rw [h_frac ⟨comap e he y.1, hUV y.2⟩]
  exact localMap_mk e he _ _ rfl _

set_option maxHeartbeats 800000 in
theorem isLocallyFraction_sectionMapFun
    (hUV : V.1 ⊆ comap e he ⁻¹' U.1)
    (s : ∀ x : U, AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)
    (hs : (AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred s) :
    (AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isLocallyFraction ℬ).pred
      (sectionMapFun e he U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨comap e he p, hUV hpV⟩ with ⟨W, m, iWU, hW⟩
  refine ⟨W.comap (comap e he) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, ?_⟩
  exact isFraction_sectionMapFun e he W (W.comap (comap e he) ⊓ V)
    (fun _ hq ↦ hq.1) (fun x : W ↦ s (iWU x)) hW

def sectionMap (hUV : V.1 ⊆ comap e he ⁻¹' U.1) :
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op U) →+*
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf ℬ).1.obj (op V) where
  toFun s := ⟨sectionMapFun e he U V hUV s.1,
    isLocallyFraction_sectionMapFun e he U V hUV s.1 s.2⟩
  map_one' := by ext; simp [sectionMapFun]
  map_zero' := by ext; simp [sectionMapFun]
  map_add' x y := by ext; simp [sectionMapFun]
  map_mul' x y := by ext; simp [sectionMapFun]

end Sections

def sheafedSpaceMap : Proj.toSheafedSpace ℬ ⟶ Proj.toSheafedSpace 𝒜 where
  base := TopCat.ofHom (comap e he)
  c := { app U := CommRingCat.ofHom (sectionMap e he _ _ Set.Subset.rfl) }

open AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf

theorem germ_map_sectionInBasicOpen {p : ProjectiveSpectrum ℬ}
    (c : NumDenSameDeg 𝒜 (comapPoint e he p).asHomogeneousIdeal.toIdeal.primeCompl) :
    (Proj.toSheafedSpace ℬ).presheaf.germ
      ((Opens.map (sheafedSpaceMap e he).base).obj _) p (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMap e he).c.app _ (sectionInBasicOpen 𝒜 _ c)) =
    (Proj.toSheafedSpace ℬ).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ (e (c.den : A))) p c.den_mem
      (sectionInBasicOpen ℬ p
        (mapFraction e he (Q := p.asHomogeneousIdeal.toIdeal.primeCompl) le_rfl c)) := rfl

@[simp] theorem val_sectionInBasicOpen_apply (p : ProjectiveSpectrum 𝒜)
    (c : NumDenSameDeg 𝒜 p.asHomogeneousIdeal.toIdeal.primeCompl)
    (q : ProjectiveSpectrum.basicOpen 𝒜 c.den) :
    ((sectionInBasicOpen 𝒜 p c).val q).val =
      Localization.mk (c.num : A) ⟨(c.den : A), q.2⟩ := rfl

theorem localMap_comp_stalkIso (p : ProjectiveSpectrum ℬ) :
    (Proj.stalkIso 𝒜 (comap e he p)).hom ≫
      CommRingCat.ofHom (localMap e he _ _ rfl) ≫ (Proj.stalkIso ℬ p).inv =
      (sheafedSpaceMap e he).stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, Proj.stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
  simp only [val_localMap, HomogeneousLocalization.val_mk, RingHom.comp_apply, RingHom.coe_coe]
  erw [Proj.stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germ_map_sectionInBasicOpen]
  erw [Proj.stalkIso'_germ]
  simp [mapFraction, degreeAddHom, Localization.localRingHom,
    Localization.mk_eq_mk', IsLocalization.map_mk']

/-- The actual contravariant Proj morphism induced by the ring equivalence. -/
def map : Proj ℬ ⟶ Proj 𝒜 where
  __ := sheafedSpaceMap e he
  prop p := IsLocalHom.mk fun x hx ↦ by
    rw [← localMap_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (Proj.stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (Proj.stalkIso 𝒜 (comap e he p)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

@[simp] theorem map_preimage_basicOpen (s : A) :
    map e he ⁻¹ᵁ Proj.basicOpen 𝒜 s = Proj.basicOpen ℬ (e s) := rfl

theorem powers_le_comap (s : A) (t : B) (h : e s = t) :
    Submonoid.powers s ≤ (Submonoid.powers t).comap e.toRingHom := by
  rintro a ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  change t ^ n = e (s ^ n)
  rw [map_pow, h]

def awayMap (s : A) (t : B) (h : e s = t) : Away 𝒜 s →+* Away ℬ t :=
  HomogeneousLocalization.map 𝒜 ℬ e.toRingHom (powers_le_comap e s t h)
    (fun n a ha ↦ (he n a).mp ha)

private theorem ext_toSpec {X : Scheme.{u}} {S : Type u} [CommRing S]
    {f g : X ⟶ Spec (.of S)}
    (h : (Scheme.ΓSpecIso (.of S)).inv ≫ Scheme.Γ.map f.op =
      (Scheme.ΓSpecIso (.of S)).inv ≫ Scheme.Γ.map g.op) : f = g :=
  (ΓSpec.adjunction.homEquiv X (op (.of S))).symm.injective (unop_injective h)

@[simp] private theorem resLE_app_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) {h} :
    (f.resLE V U h).app ⊤ = V.topIso.hom ≫ f.appLE V U h ≫ U.topIso.inv := by
  simp [Scheme.Hom.resLE]

theorem awayToSection_comp_appLE (s : A) :
    Proj.awayToSection 𝒜 s ≫
      (map e he).appLE (Proj.basicOpen 𝒜 s) (Proj.basicOpen ℬ (e s)) le_rfl =
    CommRingCat.ofHom (awayMap e he s (e s) rfl) ≫ Proj.awayToSection ℬ (e s) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
  apply Subtype.ext
  funext p
  change HomogeneousLocalization.mk _ = HomogeneousLocalization.mk _
  rfl

/-- The map agrees with the original homogeneous-localization map on every chart. -/
@[reassoc] theorem awayι_comp_map {n : ℕ} (hn : 0 < n)
    (s : A) (hs : s ∈ 𝒜 n) (t : B) (h : e s = t) :
    Proj.awayι ℬ t (h ▸ (he n s).mp hs) hn ≫ map e he =
      Spec.map (CommRingCat.ofHom (awayMap e he s t h)) ≫ Proj.awayι 𝒜 s hs hn := by
  subst t
  have hi : (Proj.basicOpen ℬ (e s)).ι ≫ map e he =
      (map e he).resLE _ _ le_rfl ≫ (Proj.basicOpen 𝒜 s).ι := by simp
  rw [Proj.awayι, Proj.awayι, Category.assoc, hi, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_toSpec ((cancel_mono (Proj.basicOpen ℬ (e s)).topIso.hom).mp ?_)
  simp [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top,
    awayToSection_comp_appLE]

theorem awayMap_symm_comp (s : A) (t : B) (h : e s = t) :
    (awayMap e.symm (preservesDegrees_symm e he) t s
      (by rw [← h, RingEquiv.symm_apply_apply])).comp
      (awayMap e he s t h) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
  apply HomogeneousLocalization.val_injective
  simp [awayMap, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]

theorem map_symm_comp :
    map e.symm (preservesDegrees_symm e he) ≫ map e he = 𝟙 (Proj 𝒜) := by
  refine (Proj.affineOpenCover 𝒜).openCover.hom_ext _ _ fun s ↦ ?_
  change Proj.awayι 𝒜 (s.2 : A) s.2.2 s.1.2 ≫
      (map e.symm (preservesDegrees_symm e he) ≫ map e he) =
    Proj.awayι 𝒜 (s.2 : A) s.2.2 s.1.2 ≫ 𝟙 _
  rw [← Category.assoc,
    awayι_comp_map e.symm (preservesDegrees_symm e he) s.1.2 (e s.2)
      ((he _ _).mp s.2.2) s.2 (e.symm_apply_apply s.2),
    Category.assoc, awayι_comp_map e he s.1.2 s.2 s.2.2 (e s.2) rfl,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  rw [awayMap_symm_comp e he]
  simp

/-- The actual scheme isomorphism, covariant in the displayed ring equivalence. -/
def iso : Proj 𝒜 ≅ Proj ℬ where
  hom := map e.symm (preservesDegrees_symm e he)
  inv := map e he
  hom_inv_id := map_symm_comp e he
  inv_hom_id := map_symm_comp e.symm (preservesDegrees_symm e he)

def zeroMap : 𝒜 0 →+* ℬ 0 where
  toFun a := ⟨e a, (he 0 a).mp a.2⟩
  map_one' := by ext; exact map_one e
  map_zero' := by ext; exact map_zero e
  map_add' a b := by ext; exact map_add e (a : A) (b : A)
  map_mul' a b := by ext; exact map_mul e (a : A) (b : A)

theorem awayMap_comp_fromZeroRingHom (s : A) (t : B) (h : e s = t) :
    (awayMap e he s t h).comp (fromZeroRingHom 𝒜 (Submonoid.powers s)) =
      (fromZeroRingHom ℬ (Submonoid.powers t)).comp (zeroMap e he) := by
  apply RingHom.ext
  intro a
  apply HomogeneousLocalization.val_injective
  simp [awayMap, fromZeroRingHom, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, zeroMap]

/-- Compatibility with the original structure map to the degree-zero ring. -/
@[reassoc] theorem map_comp_toSpecZero :
    map e he ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (zeroMap e he)) := by
  refine (Proj.affineOpenCover ℬ).openCover.hom_ext _ _ fun s ↦ ?_
  change Proj.awayι ℬ (s.2 : B) s.2.2 s.1.2 ≫ (map e he ≫ Proj.toSpecZero 𝒜) =
    Proj.awayι ℬ (s.2 : B) s.2.2 s.1.2 ≫
      (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (zeroMap e he)))
  rw [← Category.assoc, awayι_comp_map e he s.1.2 (e.symm s.2)
    ((preservesDegrees_symm e he _ _).mp s.2.2) s.2 (e.apply_symm_apply s.2)]
  rw [Category.assoc, Proj.awayι_toSpecZero, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    awayMap_comp_fromZeroRingHom]

@[reassoc] theorem iso_hom_comp_toSpecZero :
    (iso e he).hom ≫ Proj.toSpecZero ℬ =
      Proj.toSpecZero 𝒜 ≫
        Spec.map (CommRingCat.ofHom (zeroMap e.symm (preservesDegrees_symm e he))) :=
  map_comp_toSpecZero e.symm (preservesDegrees_symm e he)

/-- Compatibility over any original base with compatible degree-zero coefficient maps. -/
theorem iso_hom_comp_toSpecBase {S : Type u} [CommRing S]
    (a : S →+* 𝒜 0) (b : S →+* ℬ 0)
    (hab : (zeroMap e.symm (preservesDegrees_symm e he)).comp b = a) :
    (iso e he).hom ≫ (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom b)) =
      Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom a) := by
  rw [← Category.assoc, iso_hom_comp_toSpecZero, Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hab]

end KltDP.GradedProjIso
