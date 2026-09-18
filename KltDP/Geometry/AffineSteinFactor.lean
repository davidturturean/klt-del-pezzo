/-
The surjectivity argument is adapted from Mathlib Morphisms/Proper.lean.
Copyright (c) 2024 Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.ProperAffineSectionsFinite
import KltDP.Geometry.AffinizationStructureSheaf
import KltDP.Geometry.SteinTargetIntegral

/-!
# Geometry of the original affine Stein factor

For a proper map to an affine base, use the original affinization map
and its original scalar-map factor. Properness, surjectivity and the
canonical pushforward structure-sheaf isomorphism are ordinary consequences
of the pinned Gamma-Spec comparison. Over a Noetherian base, the already
proved original section-algebra finiteness makes the second map finite.
No geometric connectedness or global relative-spectrum gluing is asserted.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ProperAffineSections

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [hproper : IsProper f]

include f hproper

/-- The original affinization map of a proper affine-base scheme is proper. -/
theorem toSpecΓ_isProper : IsProper X.toSpecΓ := by
  letI : IsProper (X.toSpecΓ ≫ toSpecBase f) := by
    rw [toSpecΓ_toSpecBase]
    infer_instance
  exact IsProper.of_comp_of_isSeparated X.toSpecΓ (toSpecBase f)

/-- Its image is closed, and its original global-section map is injective. -/
theorem toSpecΓ_surjective : Surjective X.toSpecΓ := by
  letI : CompactSpace X := (quasiCompact_over_affine_iff f).mp inferInstance
  letI : IsProper X.toSpecΓ := toSpecΓ_isProper f
  constructor
  apply surjective_of_isClosed_range_of_injective
  · exact X.toSpecΓ.isClosedMap.isClosed_range
  · simp only [Scheme.toSpecΓ_appTop]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(X, ⊤)).hom).1

/-- The actual canonical structure-sheaf map is an isomorphism on all opens. -/
theorem toSpecΓ_structure_isIso : IsIso X.toSpecΓ.c := by
  letI : CompactSpace X := (quasiCompact_over_affine_iff f).mp inferInstance
  letI : QuasiSeparatedSpace X := (quasiSeparated_over_affine_iff f).mp inferInstance
  exact AffinizationStructureSheaf.toSpecΓ_c_isIso X

/-- The same original factorization has all these properties simultaneously. -/
theorem affine_factor_geometry [IsNoetherianRing R] :
    X.toSpecΓ ≫ toSpecBase f = f ∧ IsProper X.toSpecΓ ∧
      Surjective X.toSpecΓ ∧ IsFinite (toSpecBase f) ∧ IsIso X.toSpecΓ.c :=
  ⟨toSpecΓ_toSpecBase f, toSpecΓ_isProper f, toSpecΓ_surjective f,
    toSpecBase_isFinite f, toSpecΓ_structure_isIso f⟩

/-- For the integral normal source used in the manuscript, this original
affine target is integral and normal as a derived conclusion. -/
theorem affine_target_integral_normal [IsIntegral X] (hnormal : IsNormalScheme X) :
    IsIntegral (Spec Γ(X, ⊤)) ∧ IsNormalScheme (Spec Γ(X, ⊤)) := by
  letI : IsIso X.toSpecΓ.c := toSpecΓ_structure_isIso f
  exact SteinTargetIntegral.integral_and_normal X.toSpecΓ hnormal
    (toSpecΓ_surjective f).surj

end KltDP.Geometry.ProperAffineSections
