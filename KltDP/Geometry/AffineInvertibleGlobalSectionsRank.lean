import KltDP.Geometry.AffineInvertibleGlobalSectionsFinite
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Rank of the original affine invertible global sections

A basic open inside a chart containing the generic point has a nonzero
denominator. The original restriction to that open is a localization of
the original global-section module. The pinned localization rank
theorems compare this rank with the rank over the actual section ring;
the original chart isomorphism then makes that rank one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory
variable {R : Type u} [CommRing R] [IsDomain R]

local instance rankSectionRingAlgebraInst {A : Type u} [CommRing A]
    (W : (Spec (.of A)).Opens) :
    Algebra A (Γ(Spec (.of A), W)) :=
  finiteSectionRingAlgebra W

local instance rankBasicOpenLocalizationInst {A : Type u} [CommRing A] (r : A) :
    IsLocalization.Away r (Γ(Spec (.of A), PrimeSpectrum.basicOpen r)) :=
  finiteBasicOpenLocalization r

local instance rankSectionModuleOverRingInst {A : Type u} [CommRing A]
    (M : (Spec (.of A)).Modules) (W : (Spec (.of A)).Opens) :
    Module (Γ(Spec (.of A), W)) (sectionModule M W) :=
  sectionModuleOverRing M W

local instance rankSectionModuleOverRingTowerInst {A : Type u} [CommRing A]
    (M : (Spec (.of A)).Modules) (W : (Spec (.of A)).Opens) :
    IsScalarTower A (Γ(Spec (.of A), W)) (sectionModule M W) :=
  sectionModuleOverRingTower M W

/-- A chart containing the actual generic point contains a basic open with nonzero denominator. -/
theorem exists_nonzero_chartBasicElement
    (M : (Spec (.of R)).Modules)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := (Spec (.of R)).ringCatSheaf) M) :
    ∃ (i : t.I) (g : R), g ≠ 0 ∧ PrimeSpectrum.basicOpen g ≤ t.X i := by
  have hx : (⊥ : PrimeSpectrum R) ∈ ⨆ i, t.X i := by
    rw [TransitionUnitExtraction.chartOpens_cover (Spec (.of R)) M t]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgi⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (t.X i).isOpen
  refine ⟨i, g, ?_, hgi⟩
  rintro rfl
  simpa only [PrimeSpectrum.basicOpen_zero, Opens.mem_bot] using hxg

/-- The original global-section module has rank one over the original domain. -/
theorem globalSections_rank_of_localTrivializations
    (M : (Spec (.of R)).Modules)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := (Spec (.of R)).ringCatSheaf) M) :
    Module.rank R (sectionModule M ⊤) = 1 := by
  obtain ⟨i, g, hg, hgi⟩ := exists_nonzero_chartBasicElement M t
  let W : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen g
  let S : Type u := Γ(Spec (.of R), W)
  let f : sectionModule M ⊤ →ₗ[R] sectionModule M W :=
    (sectionRestrict M (le_top : W ≤ ⊤)).hom
  letI : IsLocalizedModule (Submonoid.powers g) f :=
    localized_of_denominatorExtension_top M
      (denominatorExtension_top_of_localTrivializations M t) g
  have hp : Submonoid.powers g ≤ nonZeroDivisors R := by
    rintro a ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hg)
  letI : Nontrivial S := (IsLocalization.injective S hp).nontrivial
  calc
    Module.rank R (sectionModule M ⊤) = Module.rank R (sectionModule M W) :=
      (IsLocalizedModule.rank_eq (p := Submonoid.powers g) (hp := hp) f).symm
    _ = Module.rank S (sectionModule M W) :=
      (IsLocalization.rank_eq S (Submonoid.powers g) hp).symm
    _ = Module.rank S S :=
      (TransitionUnitExtraction.chartEquiv (Spec (.of R)) M t i hgi).rank_eq
    _ = 1 := Module.rank_self S

/-- The original global-section module of an affine invertible sheaf has rank one. -/
theorem invertibleGlobalSections_rank (L : InvertibleSheaf (Spec (.of R))) :
    Module.rank R (sectionModule L.obj ⊤) = 1 :=
  globalSections_rank_of_localTrivializations L.obj L.localTrivializations

/-- The finite rank used by the pinned PID basis theorem is exactly one. -/
theorem invertibleGlobalSections_finrank (L : InvertibleSheaf (Spec (.of R))) :
    Module.finrank R (sectionModule L.obj ⊤) = 1 := by
  simpa only [Module.finrank, Cardinal.one_toNat] using
    congrArg Cardinal.toNat (invertibleGlobalSections_rank L)

end KltDP.Geometry.AffineModuleTilde
