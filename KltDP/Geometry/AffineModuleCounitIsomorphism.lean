import KltDP.Geometry.AffineModuleCounit
import KltDP.Geometry.AffineModuleDenominators
import KltDP.Compatibility.SheafIsoOnBasis

/-!
# Detecting the actual affine counit isomorphism by denominator extension

When the original global restrictions satisfy module localization, their
canonical lifts are the unique localization equivalences on each basic
open. The actual module-sheaf basis criterion then proves that the original
counit is an isomorphism. The hypotheses refer to the original restrictions,
not to supplied comparison maps or replacement section modules.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R] (M : (Spec (.of R)).Modules)

/-- Actual localized global restriction makes the original counit bijective on D(f). -/
theorem counit_basicOpen_bijective_of_localized (f : R)
    (h : IsLocalizedModule (Submonoid.powers f)
      (sectionRestrict M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).hom) :
    Function.Bijective ((counit M).val.app (op (PrimeSpectrum.basicOpen f))) := by
  letI := h
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f)).hom
    (sectionRestrict M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).hom
  have he : (counitBasicOpen M f).hom = e.toLinearMap := by
    apply IsLocalizedModule.ext (Submonoid.powers f)
      (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f)).hom
      (sectionScalar_map_units M f le_rfl)
    apply LinearMap.ext
    intro m
    change counitBasicOpen M f
        (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f) m) =
      e (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f) m)
    rw [counitBasicOpen_toOpen]
    exact (IsLocalizedModule.linearEquiv_apply (Submonoid.powers f)
      (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f)).hom
      (sectionRestrict M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).hom m).symm
  have hfun :
      (fun s : (sectionModule M ⊤).tilde.val.obj (op (PrimeSpectrum.basicOpen f)) =>
        (counit M).val.app (op (PrimeSpectrum.basicOpen f)) s) = (fun s => e s) := by
    funext s
    rw [counit_app_apply, counitModuleSheaf_basicOpen_app]
    exact DFunLike.congr_fun he s
  change Function.Bijective
    (fun s : (sectionModule M ⊤).tilde.val.obj (op (PrimeSpectrum.basicOpen f)) =>
      (counit M).val.app (op (PrimeSpectrum.basicOpen f)) s)
  rw [hfun]
  exact e.bijective

/-- The actual original counit is an isomorphism when global restrictions localize. -/
theorem counit_isIso_of_localized
    (h : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (sectionRestrict M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).hom) :
    IsIso (counit M) :=
  KltDP.SheafOfModules.isIso_of_bijective_on_basis (counit M)
    PrimeSpectrum.isBasis_basic_opens (fun f => counit_basicOpen_bijective_of_localized M f (h f))

/-- Denominator extension proves invertibility of the actual original counit. -/
theorem counit_isIso_of_denominatorExtension (h : DenominatorExtension M ⊤) :
    IsIso (counit M) :=
  counit_isIso_of_localized M (localized_of_denominatorExtension_top M h)

end KltDP.Geometry.AffineModuleTilde
