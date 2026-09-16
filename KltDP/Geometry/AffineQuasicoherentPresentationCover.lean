/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

The presentation refinement follows official Mathlib Tilde.lean:850–873
at 79d0395a1825a6264ad5d269e35e60537518955e. Actual project restriction
and pullback comparisons replace the later restriction-composition API.
-/
import KltDP.Geometry.QuasicoherentOpenPresentation
import KltDP.Geometry.AffineModuleBasicOpenDenominators
import KltDP.Geometry.ModuleRestrictionPullback
import KltDP.Geometry.ModuleOpenRestrictionTensor
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Finite basic-open presentations of an original quasicoherent sheaf

An actual presentation restricts along an open immersion because the
original restriction is a left adjoint and preserves the actual unit.
For D(g), the localization map's original image factorization compares
this restriction with restriction to Spec(R_g). The original affine
presentation cover can therefore be refined to a finite basic-open
cover carrying presentations on the actual localized schemes.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

open SchemeModuleRestriction AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Restrict an actual presentation through the original colimit-preserving functor. -/
def presentationOpenRestriction {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (P : M.Presentation) : ((restriction f).obj M).Presentation := by
  letI : PreservesColimitsOfSize.{u, u} (restriction f) :=
    (restrictionAdjunction f).leftAdjoint_preservesColimits
  exact P.map (restriction f) (restrictionUnitIso f).symm

namespace AffineModuleTilde

variable {R : Type u} [CommRing R]

/-- The actual localization map identifies its source with the original basic open. -/
def awayOpenIso (g : R) :
    Spec (.of (Localization.Away g)) ≅
      Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen g) :=
  (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))).isoOpensRange ≪≫
    (Spec (.of R)).isoOfEq (awayRestriction_opensRange g)

/-- This identification retains the literal localization projection. -/
theorem awayOpenIso_hom_ι (g : R) :
    (awayOpenIso g).hom ≫ Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen g) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))) := by
  simp only [awayOpenIso, Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι, Scheme.Hom.isoOpensRange_hom_ι]

variable (M : (Spec (.of R)).Modules)

/-- An original open presentation restricts to the actual localized affine scheme. -/
def awayPresentationOfOpen (g : R) (U : (Spec (.of R)).Opens)
    (h : PrimeSpectrum.basicOpen g ≤ U)
    (P : ((restriction U.ι).obj M).Presentation) :
    ((restriction (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away g))))).obj M).Presentation := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))
  let t := (awayOpenIso g).hom ≫ (Spec (.of R)).homOfLE h
  have ht : t ≫ U.ι = j := by
    dsimp only [t, j]
    rw [Category.assoc, Scheme.homOfLE_ι, awayOpenIso_hom_ι]
  let e : (restriction U.ι ⋙ restriction t).obj M ≅ (restriction j).obj M :=
    (isoWhiskerRight (restrictionIsoPullback U.ι) (restriction t) ≪≫
      isoWhiskerLeft (schemeModulePullback U.ι) (restrictionIsoPullback t) ≪≫
      schemeModulePullbackCompIso t U.ι ≪≫
      eqToIso (congrArg schemeModulePullback ht) ≪≫
      (restrictionIsoPullback j).symm).app M
  exact _root_.SheafOfModules.Presentation.ofIsIso e.hom
    (presentationOpenRestriction t ((restriction U.ι).obj M) P)

/-- Every original quasicoherent affine module has a finite basic-open cover
with actual presentations on the corresponding localized affine schemes. -/
theorem exists_finite_away_presentations [M.IsQuasicoherent] :
    ∃ (I : Type u) (_ : Fintype I) (g : I → R),
      ((⊤ : (Spec (.of R)).Opens) = ⨆ i, PrimeSpectrum.basicOpen (g i)) ∧
      Nonempty (∀ i, ((restriction (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (g i)))))).obj M).Presentation) := by
  classical
  obtain ⟨I, U, _, hU, ⟨P⟩⟩ := exists_affine_open_presentations M
  have hlocal (x : Spec (.of R)) :
      ∃ (g : R) (i : I), x ∈ PrimeSpectrum.basicOpen g ∧ PrimeSpectrum.basicOpen g ≤ U i := by
    obtain ⟨i, hxi⟩ := hU x
    obtain ⟨_, ⟨g, rfl⟩, hxg, hgU⟩ :=
      (Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) hxi
    exact ⟨g, i, hxg, hgU⟩
  choose g i hxg hgU using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : Spec (.of R) => (PrimeSpectrum.basicOpen (g x) : Set (PrimeSpectrum R)))
    (fun x => (PrimeSpectrum.basicOpen (g x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxg x⟩)
  refine ⟨↥s, inferInstance, fun x => g x, ?_, ⟨fun x => ?_⟩⟩
  · apply le_antisymm ?_ le_top
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩
  · exact awayPresentationOfOpen M (g x) (U (i x)) (hgU x) (P (i x))

end AffineModuleTilde

end KltDP.Geometry
