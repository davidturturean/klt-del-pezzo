/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

The denominator-extension conditions and their restriction lemma follow
QuasicoherentTilde.Aux in Mathlib at
633b366493a76df88a2bff099ed0cbf711a59ec9. All section modules and maps
below are the original pinned sheaf objects with their canonical R-actions.
-/
import KltDP.Geometry.AffineModuleGlobalSections

/-!
# Denominator extension for original affine module sheaves

These two properties express extension and detection of zero after
multiplication by a power of a defining function. Their restriction to a
smaller basic open follows using only the actual invertibility of that
basic open's defining function. They are intermediate proved properties,
not an assumed affine reconstruction isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R] (M : (Spec (.of R)).Modules)

/-- The original section restrictions compose as maps of R-modules. -/
theorem sectionRestrict_comp {U V W : (Spec (.of R)).Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : sectionModule M U) :
    sectionRestrict M hWV (sectionRestrict M hVU s) =
      sectionRestrict M (hWV.trans hVU) s := by
  change (((modulesSpecToSheaf R).obj M).val.map (homOfLE hVU).op ≫
    ((modulesSpecToSheaf R).obj M).val.map (homOfLE hWV).op) s = _
  rw [← Functor.map_comp]
  rfl

/-- Powers of a function are cancellable on actual sections of any subopen of D(f). -/
theorem sectionScalar_pow_smul_injective (f : R) {U : (Spec (.of R)).Opens}
    (hU : U ≤ PrimeSpectrum.basicOpen f) (n : ℕ) :
    Function.Injective (fun s : sectionModule M U => f ^ n • s) := by
  have h := sectionScalar_map_units M f hU (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
  exact ((Module.End.isUnit_iff _).mp h).injective

/-- Extension and zero detection by powers of a basic-open defining function. -/
structure DenominatorExtension (V : (Spec (.of R)).Opens) : Prop where
  existence (f : R) (hf : PrimeSpectrum.basicOpen f ≤ V)
    (s : sectionModule M (PrimeSpectrum.basicOpen f)) :
    ∃ (n : ℕ) (t : sectionModule M V), sectionRestrict M hf t = f ^ n • s
  uniqueness (f : R) (hf : PrimeSpectrum.basicOpen f ≤ V) (t : sectionModule M V) :
    sectionRestrict M hf t = 0 → ∃ n : ℕ, f ^ n • t = 0

/-- Denominator extension restricts to every actual contained basic open. -/
theorem DenominatorExtension.of_le {V : (Spec (.of R)).Opens}
    (g : R) (hg : PrimeSpectrum.basicOpen g ≤ V) (hV : DenominatorExtension M V) :
    DenominatorExtension M (PrimeSpectrum.basicOpen g) where
  existence f hfg s := by
    obtain ⟨n, t, ht⟩ := hV.existence f (hfg.trans hg) s
    exact ⟨n, sectionRestrict M hg t, by rw [sectionRestrict_comp]; exact ht⟩
  uniqueness f hfg t ht := by
    obtain ⟨n, t', ht'⟩ := hV.existence g hg t
    have hzero : sectionRestrict M (hfg.trans hg) t' = 0 := by
      rw [← sectionRestrict_comp M hg hfg, ht', sectionRestrict_smul, ht, smul_zero]
    obtain ⟨m, hm⟩ := hV.uniqueness f (hfg.trans hg) t' hzero
    refine ⟨m, ?_⟩
    apply sectionScalar_pow_smul_injective M g le_rfl n
    change g ^ n • (f ^ m • t) = g ^ n • (0 : sectionModule M (PrimeSpectrum.basicOpen g))
    rw [smul_zero, smul_comm, ← ht', ← sectionRestrict_smul, hm, map_zero]

/-- Localization of the original global restrictions implies denominator extension at the top. -/
theorem denominatorExtension_top_of_localized
    (h : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (sectionRestrict M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).hom) :
    DenominatorExtension M ⊤ where
  existence f hf s := by
    letI := h f
    obtain ⟨⟨m, a⟩, ha⟩ := IsLocalizedModule.surj (Submonoid.powers f)
      (sectionRestrict M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).hom s
    obtain ⟨n, hn⟩ := a.property
    refine ⟨n, m, ?_⟩
    simpa only [Submonoid.smul_def, ← hn] using ha.symm
  uniqueness f hf t ht := by
    letI := h f
    obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
      (sectionRestrict M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).hom).mp ht
    obtain ⟨n, hn⟩ := a.property
    exact ⟨n, by simpa only [Submonoid.smul_def, ← hn] using ha⟩

/-- The two denominator properties imply localization of the original global restrictions. -/
theorem localized_of_denominatorExtension_top (h : DenominatorExtension M ⊤) (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      (sectionRestrict M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).hom where
  map_units := sectionScalar_map_units M f le_rfl
  surj' s := by
    obtain ⟨n, t, ht⟩ := h.existence f le_top s
    exact ⟨(t, ⟨f ^ n, n, rfl⟩), ht.symm⟩
  exists_of_eq {x₁ x₂} hxy := by
    have hzero : sectionRestrict M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤) (x₁ - x₂) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨n, hn⟩ := h.uniqueness f le_top _ hzero
    exact ⟨⟨f ^ n, n, rfl⟩, by simpa only [Submonoid.smul_def, smul_sub, sub_eq_zero] using hn⟩

end KltDP.Geometry.AffineModuleTilde
