import KltDP.Geometry.AffineInvertibleGlobalSectionsFinite
import KltDP.Compatibility.FlatModuleTorsionFree
import Mathlib.RingTheory.Flat.Localization

/-!
# Flatness of the original affine global-section module

On each actual rank-one chart, the base-ring module of sections is
linearly equivalent to the actual localized section ring. Those rings are
flat by the pinned localization theorem. The pinned descent theorem for
flatness applies to the original global restriction maps and proves
flatness globally. Over a domain this also gives torsion-freeness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory
variable {R : Type u} [CommRing R]

local instance flatSectionRingAlgebraInst (W : (Spec (.of R)).Opens) :
    Algebra R (Γ(Spec (.of R), W)) :=
  finiteSectionRingAlgebra W

local instance flatBasicOpenLocalizationInst (r : R) :
    IsLocalization.Away r (Γ(Spec (.of R), PrimeSpectrum.basicOpen r)) :=
  finiteBasicOpenLocalization r

/-- Actual local rank-one trivializations imply flatness of original global sections. -/
theorem globalSections_flat_of_localTrivializations
    (M : (Spec (.of R)).Modules)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := (Spec (.of R)).ringCatSheaf) M) :
    Module.Flat R (sectionModule M ⊤) := by
  let S := chartBasicElements M t
  let Mₛ (g : S) : Type u := sectionModule M (PrimeSpectrum.basicOpen g.val)
  letI : ∀ g : S, AddCommMonoid (Mₛ g) :=
    fun g => inferInstanceAs (AddCommMonoid (sectionModule M (PrimeSpectrum.basicOpen g.val)))
  letI : ∀ g : S, Module R (Mₛ g) :=
    fun g => (sectionModule M (PrimeSpectrum.basicOpen g.val)).isModule
  letI : ∀ g : S, IsScalarTower R R (Mₛ g) :=
    fun _ => inferInstance
  let f (g : S) : sectionModule M ⊤ →ₗ[R] Mₛ g :=
    (sectionRestrict M (le_top : PrimeSpectrum.basicOpen g.val ≤ ⊤)).hom
  letI : ∀ g : S, IsLocalizedModule (Submonoid.powers g.val) (f g) :=
    fun g => localized_of_denominatorExtension_top M
      (denominatorExtension_top_of_localTrivializations M t) g.val
  apply Module.flat_of_isLocalized_span (R := R) (S := R) (M := sectionModule M ⊤)
    (s := S) (spn := chartBasicElements_span M t) (Mₛ := Mₛ) (g := f)
  intro g
  obtain ⟨i, hgi⟩ := g.property
  letI : Module.Flat R (Γ(Spec (.of R), PrimeSpectrum.basicOpen g.val)) :=
    IsLocalization.flat (Γ(Spec (.of R), PrimeSpectrum.basicOpen g.val)) (Submonoid.powers g.val)
  exact Module.Flat.of_linearEquiv (chartSectionLinearEquiv M t i hgi)

/-- The actual global-section module of an affine invertible sheaf is flat. -/
theorem invertibleGlobalSections_flat (L : InvertibleSheaf (Spec (.of R))) :
    Module.Flat R (sectionModule L.obj ⊤) :=
  globalSections_flat_of_localTrivializations L.obj L.localTrivializations

/-- Over a domain, original affine invertible global sections have no scalar torsion. -/
theorem invertibleGlobalSections_noZeroSMulDivisors [IsDomain R]
    (L : InvertibleSheaf (Spec (.of R))) : NoZeroSMulDivisors R (sectionModule L.obj ⊤) := by
  letI := invertibleGlobalSections_flat L
  exact KltDP.Compatibility.FlatModuleTorsionFree.noZeroSMulDivisors_of_flat R
    (sectionModule L.obj ⊤)

end KltDP.Geometry.AffineModuleTilde
