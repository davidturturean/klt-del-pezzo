import KltDP.Geometry.AffineInvertibleCounit
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finite generation of the original affine global sections

The basic opens contained in the original rank-one charts generate the
unit ideal. On each such open the original chart equivalence identifies
the section module with its section ring. The original global restriction
is a module localization by denominator extension. The pinned local
finiteness theorem therefore proves finite generation of global sections.

The section-ring actions below are the original actions. Their declarations
are used as local instances only; the canonical base-ring actions are kept.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R]

-- Use the original structure-sheaf algebra and basic-open localization.
local instance finiteSectionRingAlgebra (W : (Spec (.of R)).Opens) :
    Algebra R (Γ(Spec (.of R), W)) :=
  StructureSheaf.openAlgebra R (op W)

local instance finiteBasicOpenLocalization (r : R) :
    IsLocalization.Away r (Γ(Spec (.of R), PrimeSpectrum.basicOpen r)) :=
  StructureSheaf.IsLocalization.to_basicOpen R r

-- The canonical section map uses this definitionally equal ring presentation.
local instance finiteStructureSheafModule (M : (Spec (.of R)).Modules)
    (W : (Spec (.of R)).Opens) :
    Module ((Spec.structureSheaf R).val.obj (op W)) (sectionModule M W) :=
  (M.val.obj (op W)).isModule

/-- The original section-ring action on the original section carrier. -/
def sectionModuleOverRing (M : (Spec (.of R)).Modules) (W : (Spec (.of R)).Opens) :
    Module (Γ(Spec (.of R), W)) (sectionModule M W) :=
  (M.val.obj (op W)).isModule

local instance finiteSectionModuleOverRingInst
    (M : (Spec (.of R)).Modules) (W : (Spec (.of R)).Opens) :
    Module (Γ(Spec (.of R), W)) (sectionModule M W) :=
  sectionModuleOverRing M W

/-- The canonical R-action is the restriction of the original section-ring action. -/
theorem sectionModuleOverRingTower (M : (Spec (.of R)).Modules)
    (W : (Spec (.of R)).Opens) :
    IsScalarTower R (Γ(Spec (.of R), W)) (sectionModule M W) :=
  IsScalarTower.of_algebraMap_smul (R := R) (A := Γ(Spec (.of R), W))
    (M := sectionModule M W) (fun r s => (sectionModule_smul_toOpen M W r s).symm)

local instance finiteSectionModuleOverRingTowerInst
    (M : (Spec (.of R)).Modules) (W : (Spec (.of R)).Opens) :
    IsScalarTower R (Γ(Spec (.of R), W)) (sectionModule M W) :=
  sectionModuleOverRingTower M W

variable (M : (Spec (.of R)).Modules)
  (t : KltDP.SheafOfModules.LocalTrivializations (R := (Spec (.of R)).ringCatSheaf) M)

/-- The actual chart equivalence, also linear for the canonical base-ring actions. -/
def chartSectionLinearEquiv (i : t.I) {W : (Spec (.of R)).Opens} (hWi : W ≤ t.X i) :
    sectionModule M W ≃ₗ[R] Γ(Spec (.of R), W) :=
  (show sectionModule M W ≃ₗ[Γ(Spec (.of R), W)] Γ(Spec (.of R), W) from
    TransitionUnitExtraction.chartEquiv (Spec (.of R)) M t i hWi).restrictScalars R

@[simp]
theorem chartSectionLinearEquiv_apply (i : t.I) {W : (Spec (.of R)).Opens}
    (hWi : W ≤ t.X i) (s : sectionModule M W) :
    chartSectionLinearEquiv M t i hWi s =
      TransitionUnitExtraction.chartEquiv (Spec (.of R)) M t i hWi s := rfl

/-- Functions whose basic opens lie inside one of the original rank-one charts. -/
def chartBasicElements : Set R :=
  {g | ∃ i : t.I, PrimeSpectrum.basicOpen g ≤ t.X i}

/-- The actual trivializing cover makes its subordinate basic elements span the unit ideal. -/
theorem chartBasicElements_span : Ideal.span (chartBasicElements M t) = ⊤ := by
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
  apply top_unique
  intro x hx
  have hxchart : x ∈ ⨆ i, t.X i := by
    rw [TransitionUnitExtraction.chartOpens_cover (Spec (.of R)) M t]
    exact hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxchart
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgi⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (t.X i).isOpen
  exact Opens.mem_iSup.mpr ⟨g, Opens.mem_iSup.mpr ⟨⟨i, hgi⟩, hxg⟩⟩

include t in
/-- Original local rank-one trivializations imply finite generation of actual global sections. -/
theorem globalSections_finite_of_localTrivializations :
    Module.Finite R (sectionModule M ⊤) := by
  let S := chartBasicElements M t
  let Mₚ (g : S) : Type u := sectionModule M (PrimeSpectrum.basicOpen g.val)
  let Rₚ (g : S) : Type u := Γ(Spec (.of R), PrimeSpectrum.basicOpen g.val)
  letI (g : S) : AddCommMonoid (Mₚ g) :=
    inferInstanceAs (AddCommMonoid (sectionModule M (PrimeSpectrum.basicOpen g.val)))
  letI (g : S) : Module R (Mₚ g) :=
    (sectionModule M (PrimeSpectrum.basicOpen g.val)).isModule
  letI (g : S) : CommRing (Rₚ g) :=
    inferInstanceAs (CommRing (Γ(Spec (.of R), PrimeSpectrum.basicOpen g.val)))
  letI (g : S) : Algebra R (Rₚ g) :=
    inferInstanceAs (Algebra R (Γ(Spec (.of R), PrimeSpectrum.basicOpen g.val)))
  letI (g : S) : IsLocalization.Away g.val (Rₚ g) :=
    inferInstanceAs (IsLocalization.Away g.val
      (Γ(Spec (.of R), PrimeSpectrum.basicOpen g.val)))
  letI (g : S) : Module (Rₚ g) (Mₚ g) :=
    sectionModuleOverRing M (PrimeSpectrum.basicOpen g.val)
  letI (g : S) : IsScalarTower R (Rₚ g) (Mₚ g) :=
    sectionModuleOverRingTower M (PrimeSpectrum.basicOpen g.val)
  let f (g : S) : sectionModule M ⊤ →ₗ[R] Mₚ g :=
    (sectionRestrict M (le_top : PrimeSpectrum.basicOpen g.val ≤ ⊤)).hom
  letI (g : S) : IsLocalizedModule (Submonoid.powers g.val) (f g) :=
    localized_of_denominatorExtension_top M
      (denominatorExtension_top_of_localTrivializations M t) g.val
  refine Module.Finite.of_localizationSpan' S (chartBasicElements_span M t)
    (Mₚ := Mₚ) (Rₚ := Rₚ) f ?_
  intro g
  obtain ⟨i, hgi⟩ := g.property
  exact Module.Finite.equiv
    (TransitionUnitExtraction.chartEquiv (Spec (.of R)) M t i hgi).symm

/-- The global sections of an original invertible sheaf on Spec R form a finite R-module. -/
theorem invertibleGlobalSections_finite (L : InvertibleSheaf (Spec (.of R))) :
    Module.Finite R (sectionModule L.obj ⊤) :=
  globalSections_finite_of_localTrivializations L.obj L.localTrivializations

end KltDP.Geometry.AffineModuleTilde
