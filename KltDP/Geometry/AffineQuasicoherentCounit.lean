/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent
-/
import KltDP.Geometry.AffineQuasicoherentPresentationCover
import KltDP.Geometry.AffineModuleDenominatorDescent

/-!
# The original affine counit for arbitrary quasicoherent sheaves

The finite cover carries actual presentations on the localized schemes.
Their original denominator properties transport to the corresponding
basic opens, and the existing finite descent gives denominator extension
globally. The original counit criterion then proves that Γ(M) tilde → M
is an isomorphism. No localizing or counit-isomorphism premise is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R] (M : (Spec (.of R)).Modules) [M.IsQuasicoherent]

/-- An original quasicoherent affine module satisfies both global denominator properties. -/
theorem denominatorExtension_of_isQuasicoherent : DenominatorExtension M ⊤ := by
  obtain ⟨I, hI, g, hg, ⟨P⟩⟩ := exists_finite_away_presentations M
  letI := hI
  exact DenominatorExtension.of_finite_basicOpen_cover M ⊤ g hg
    (fun i => denominatorExtension_basicOpen_of_awayPresentation M (g i) (P i))

/-- The actual original tilde-global-sections counit is an isomorphism for every
original quasicoherent sheaf on Spec R. -/
theorem counit_isIso_of_isQuasicoherent : IsIso (counit M) :=
  counit_isIso_of_denominatorExtension M (denominatorExtension_of_isQuasicoherent M)

end KltDP.Geometry.AffineModuleTilde
