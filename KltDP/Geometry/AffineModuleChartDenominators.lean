import KltDP.Geometry.AffineModuleDenominators
import KltDP.Geometry.TransitionUnitExtraction

/-!
# Denominator extension on actual rank-one charts

The original structure sheaf has denominator extension by the pinned ring
localization theorem and the actual global-section isomorphism. Restricting
that property to D(g) and applying an original chart isomorphism proves
denominator extension for a module sheaf whenever D(g) lies in one of its
rank-one charts. The chart and every scalar action are the original ones.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R]

local instance chartSectionRingAlgebra (U : (Spec (CommRingCat.of R)).Opens) :
    Algebra R (Γ(Spec (CommRingCat.of R), U)) :=
  StructureSheaf.openAlgebra R (op U)

local instance chartBasicOpenLocalization (r : R) :
    IsLocalization.Away r (Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen r)) :=
  StructureSheaf.IsLocalization.to_basicOpen R r

/-- Ring localization proves denominator extension for the actual unit sheaf. -/
theorem unit_denominatorExtension_top (R : Type u) [CommRing R] :
    DenominatorExtension
      (_root_.SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) ⊤ where
  existence f hf s := by
    obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj
      (S := Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)) (Submonoid.powers f)
      (s : Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f))
    obtain ⟨n, hn⟩ := d.property
    refine ⟨n, (Scheme.ΓSpecIso (CommRingCat.of R)).inv a, ?_⟩
    let s' : Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f) := s
    have h : algebraMap R (Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)) a =
        algebraMap R (Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f))
          (f ^ n) * s' := by
      simpa only [← hn, mul_comm] using hd.symm
    exact h
  uniqueness f hf s hs := by
    let a : R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      (s : Γ(Spec (CommRingCat.of R), ⊤))
    have ha : (Scheme.ΓSpecIso (CommRingCat.of R)).inv a =
        (s : Γ(Spec (CommRingCat.of R), ⊤)) :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply s
    have hzero : algebraMap R (Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f))
        a = 0 := by
      change StructureSheaf.toOpen R (PrimeSpectrum.basicOpen f) a = 0
      calc
        StructureSheaf.toOpen R (PrimeSpectrum.basicOpen f) a =
            (Spec (CommRingCat.of R)).presheaf.map (homOfLE hf).op
              ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) := rfl
        _ = (Spec (CommRingCat.of R)).presheaf.map (homOfLE hf).op s :=
          congrArg ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hf).op) ha
        _ = 0 := hs
    obtain ⟨d, hd⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f)
      (Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)) a).mp hzero
    obtain ⟨n, hn⟩ := d.property
    have hna : f ^ n * a = 0 := by simpa only [← hn] using hd
    refine ⟨n, ?_⟩
    let s' : Γ(Spec (CommRingCat.of R), ⊤) := s
    have h : algebraMap R (Γ(Spec (CommRingCat.of R), ⊤)) (f ^ n) * s' = 0 := by
      rw [show s' = (Scheme.ΓSpecIso (CommRingCat.of R)).inv a from ha.symm]
      change (Scheme.ΓSpecIso (CommRingCat.of R)).inv (f ^ n) *
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv a = 0
      rw [← map_mul, hna, map_zero]
    exact h

variable (M : (Spec (CommRingCat.of R)).Modules)
  (t : KltDP.SheafOfModules.LocalTrivializations
    (R := (Spec (CommRingCat.of R)).ringCatSheaf) M)

/-- Chart coordinates respect the canonical R-actions on the original section modules. -/
private theorem chartSection_smul (i : t.I) {W : (Spec (CommRingCat.of R)).Opens}
    (hWi : W ≤ t.X i) (r : R) (s : sectionModule M W) :
    TransitionUnitExtraction.chartEquiv (Spec (CommRingCat.of R)) M t i hWi (r • s) =
      r • (TransitionUnitExtraction.chartEquiv (Spec (CommRingCat.of R)) M t i hWi s :
        sectionModule (_root_.SheafOfModules.unit
          (Spec (CommRingCat.of R)).ringCatSheaf) W) := by
  let r' : Γ(Spec (CommRingCat.of R), W) := StructureSheaf.toOpen R W r
  let s' : M.val.obj (op W) := s
  exact (TransitionUnitExtraction.chartEquiv (Spec (CommRingCat.of R)) M t i hWi).map_smul
    r' s'

/-- The chart restriction identity uses the same original restriction as the unit sheaf. -/
private theorem chartSection_restrict (i : t.I)
    {V W : (Spec (CommRingCat.of R)).Opens} (hVW : V ≤ W) (hWi : W ≤ t.X i)
    (s : sectionModule M W) :
    TransitionUnitExtraction.chartEquiv (Spec (CommRingCat.of R)) M t i
        (hVW.trans hWi) (sectionRestrict M hVW s) =
      sectionRestrict (_root_.SheafOfModules.unit
        (Spec (CommRingCat.of R)).ringCatSheaf) hVW
        (TransitionUnitExtraction.chartEquiv (Spec (CommRingCat.of R)) M t i hWi s) :=
  TransitionUnitExtraction.chartEquiv_restrict (Spec (CommRingCat.of R)) M t i hVW hWi s

/-- A basic open contained in an actual rank-one chart has denominator extension. -/
theorem denominatorExtension_basicOpen_of_chart (i : t.I) (g : R)
    (hgi : PrimeSpectrum.basicOpen g ≤ t.X i) :
    DenominatorExtension M (PrimeSpectrum.basicOpen g) := by
  let A := _root_.SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf
  have hA : DenominatorExtension A (PrimeSpectrum.basicOpen g) :=
    DenominatorExtension.of_le A g le_top (unit_denominatorExtension_top R)
  refine ⟨?_, ?_⟩
  · intro f hf s
    obtain ⟨n, a, ha⟩ := hA.existence f hf
      (TransitionUnitExtraction.chartEquiv (Spec (CommRingCat.of R)) M t i
        (hf.trans hgi) s)
    refine ⟨n, (TransitionUnitExtraction.chartEquiv
      (Spec (CommRingCat.of R)) M t i hgi).symm a, ?_⟩
    apply (TransitionUnitExtraction.chartEquiv
      (Spec (CommRingCat.of R)) M t i (hf.trans hgi)).injective
    rw [chartSection_restrict M t i hf hgi, LinearEquiv.apply_symm_apply,
      chartSection_smul M t i (hf.trans hgi)]
    exact ha
  · intro f hf s hs
    have hz : sectionRestrict A hf
        (TransitionUnitExtraction.chartEquiv (Spec (CommRingCat.of R)) M t i hgi s) = 0 := by
      rw [← chartSection_restrict M t i hf hgi, hs, map_zero]
    obtain ⟨n, hn⟩ := hA.uniqueness f hf
      (TransitionUnitExtraction.chartEquiv (Spec (CommRingCat.of R)) M t i hgi s) hz
    refine ⟨n, ?_⟩
    apply (TransitionUnitExtraction.chartEquiv (Spec (CommRingCat.of R)) M t i hgi).injective
    rw [chartSection_smul M t i hgi, map_zero]
    exact hn

end KltDP.Geometry.AffineModuleTilde
