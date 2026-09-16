/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

The counit/localization characterization follows official Mathlib
Tilde.lean:489–544 at 79d0395a1825a6264ad5d269e35e60537518955e.
Here the original canonical-section equation gives the comparison directly.
-/
import KltDP.Geometry.AffineModulePresentationCounit
import KltDP.Geometry.AffineModuleCounitIsomorphism

/-!
# Denominator extension from an actual affine presentation

Invertibility of the original counit identifies its basic-open component
with a localization equivalence through the original canonical-section
equation. Consequently an actual global presentation gives denominator
extension, ready for the existing finite-open descent argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R] (M : (Spec (.of R)).Modules)

/-- An invertible original counit makes the original global restriction
to every basic open the corresponding module localization. -/
theorem localized_of_counit_isIso [IsIso (counit M)] (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      (sectionRestrict M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).hom := by
  let E := (TopCat.Sheaf.forget (ModuleCat.{u} R) (Spec (.of R))).mapIso
    ((modulesSpecToSheaf R).mapIso (asIso (counit M)))
  let e := (E.app (op (PrimeSpectrum.basicOpen f))).toLinearEquiv
  have he : e.toLinearMap.comp
      (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f)).hom =
      (sectionRestrict M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).hom := by
    apply LinearMap.ext
    intro m
    change ((modulesSpecToSheaf R).map (counit M)).val.app
      (op (PrimeSpectrum.basicOpen f))
      (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f) m) =
        sectionRestrict M le_top m
    rw [modulesSpecToSheaf_map_counit, counitModuleSheaf_basicOpen_app]
    exact counitBasicOpen_toOpen M f m
  exact he ▸ IsLocalizedModule.of_linearEquiv
    (S := Submonoid.powers f)
    (f := (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f)).hom) e

/-- The original counit is invertible exactly when its actual global
restrictions satisfy the module-localization property. -/
theorem counit_isIso_iff_localized : IsIso (counit M) ↔
    ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (sectionRestrict M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).hom :=
  ⟨fun h => by letI := h; exact localized_of_counit_isIso M,
    counit_isIso_of_localized M⟩

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- A supplied actual presentation, with its original generators and
relations, implies the proved denominator-extension property. -/
theorem denominatorExtension_of_presentation (P : M.Presentation) :
    DenominatorExtension M ⊤ := by
  letI := counit_isIso_of_presentation R M P
  exact denominatorExtension_top_of_localized M (localized_of_counit_isIso M)

end KltDP.Geometry.AffineModuleTilde
