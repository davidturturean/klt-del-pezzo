import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite global sections over the actual base field

Mathlib's `finite_appTop_of_universallyClosed` proves finiteness over
the global sections of `Spec k`. This adapter composes with the canonical
`ΓSpecIso` to obtain the actual base-field action on `Γ(X, ⊤)`.

The input is an integral scheme with its actual universally closed,
locally finite-type structure morphism. No finiteness of sections or
cohomology is assumed. Higher coherent cohomology is outside this result.

Reuse: Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b,
`AlgebraicGeometry/Morphisms/Proper.lean`, lines 139–151, and
`RingTheory/Finiteness/Basic.lean`, `RingHom.Finite.of_surjective` and
`RingHom.Finite.comp`. The broader reuse search and its boundaries are
recorded in `docs/COHOMOLOGY_FOUNDATION_REUSE.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The scalar map determined by the original structure morphism. -/
def baseFieldToGlobalSections (f : X ⟶ Spec (CommRingCat.of k)) :
    k →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-- Finiteness after transporting the base's sections to the original field. -/
theorem baseFieldToGlobalSections_finite
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    [UniversallyClosed f] [LocallyOfFiniteType f] :
    (baseFieldToGlobalSections f).Finite := by
  apply RingHom.Finite.comp (finite_appTop_of_universallyClosed k f)
  exact RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2

/-- Global sections are a finite module for this precise base-field action. -/
theorem globalSections_moduleFinite
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    [UniversallyClosed f] [LocallyOfFiniteType f] :
    letI := (baseFieldToGlobalSections f).toAlgebra
    Module.Finite k Γ(X, ⊤) :=
  baseFieldToGlobalSections_finite f

/-- The corresponding vector space has finite dimension over the base field. -/
theorem globalSections_finiteDimensional
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    [UniversallyClosed f] [LocallyOfFiniteType f] :
    letI := (baseFieldToGlobalSections f).toAlgebra
    FiniteDimensional k Γ(X, ⊤) :=
  globalSections_moduleFinite f

end KltDP.Geometry
