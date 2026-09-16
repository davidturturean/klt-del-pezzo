/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.AffineSymmetricAlgebraSheaf
import KltDP.Compatibility.SymmetricAlgebra.Grading

/-!
# Original graded pieces of the affine symmetric algebra sheaf

Each actual homogeneous submodule is sent to its original tilde sheaf, and
its original inclusion maps to the underlying module of the actual affine
algebra sheaf. The image of its actual global-section map is exactly the
corresponding intrinsic symmetric degree under the original ΓSpec comparison.
This proves the graded section comparison using the original maps, rather
than only assigning degrees to a renamed polynomial algebra.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineSymmetricAlgebraSheaf

open AffineModuleTilde KltDP.SymmetricAlgebra

variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

/-- The actual module of homogeneous elements of degree n. -/
abbrev degreeModule (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (grading R M n)

/-- The original homogeneous inclusion as a morphism of actual sheaves. -/
def degreeInclusion (n : ℕ) :
    (degreeModule R M n).tilde ⟶ underlyingModule R (KltDP.SymmetricAlgebra R M) :=
  AffineModuleTilde.map (ModuleCat.ofHom (grading R M n).subtype) ≫
    (tildeIso R (KltDP.SymmetricAlgebra R M)).hom

/-- Its original global-section map, with the canonical R-actions. -/
def degreeGlobalMap (n : ℕ) :
    sectionModule (degreeModule R M n).tilde ⊤ →ₗ[R]
      sectionModule (underlyingModule R (KltDP.SymmetricAlgebra R M)) ⊤ :=
  ((globalSectionsFunctor R).map (degreeInclusion R M n)).hom

/-- The global degree is the image of the actual homogeneous sheaf inclusion. -/
def globalDegree (n : ℕ) :
    Submodule R (sectionModule (underlyingModule R (KltDP.SymmetricAlgebra R M)) ⊤) :=
  LinearMap.range (degreeGlobalMap R M n)

/-- The homogeneous sheaf map retains the original ΓSpec image of each element. -/
theorem degreeGlobalMap_toOpen (n : ℕ) (a : grading R M n) :
    degreeGlobalMap R M n (ModuleCat.Tilde.toOpen (degreeModule R M n) ⊤ a) =
      RationalTreePicard.componentUnitGlobalEquiv R (KltDP.SymmetricAlgebra R M) a.val := by
  change (tildeIso R (KltDP.SymmetricAlgebra R M)).hom.val.app (op ⊤)
    ((AffineModuleTilde.map (ModuleCat.ofHom (grading R M n).subtype)).val.app (op ⊤)
      (ModuleCat.Tilde.toOpen (degreeModule R M n) ⊤ a)) = _
  rw [AffineModuleTilde.map_app_toOpen]
  exact RationalTreePicard.componentUnitTildePushforwardIso_toOpen
    R (KltDP.SymmetricAlgebra R M) ⊤ a.val

/-- Actual global homogeneous sections preserve and reflect the intrinsic
symmetric degree through the original global-section isomorphism. -/
theorem globalEquiv_mem_degree_iff (n : ℕ) (a : KltDP.SymmetricAlgebra R M) :
    RationalTreePicard.componentUnitGlobalEquiv R (KltDP.SymmetricAlgebra R M) a ∈
      globalDegree R M n ↔ a ∈ grading R M n := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨b, rfl⟩ := toOpen_top_surjective (degreeModule R M n) s
    rw [degreeGlobalMap_toOpen] at hs
    have hb := (RationalTreePicard.componentUnitGlobalEquiv
      R (KltDP.SymmetricAlgebra R M)).injective hs
    exact hb ▸ b.property
  · intro ha
    exact ⟨ModuleCat.Tilde.toOpen (degreeModule R M n) ⊤ ⟨a, ha⟩,
      degreeGlobalMap_toOpen R M n ⟨a, ha⟩⟩

/-- The original generators have degree one in the actual sheaf grading. -/
theorem generator_global_mem_degree_one (m : M) :
    RationalTreePicard.componentUnitGlobalEquiv R (KltDP.SymmetricAlgebra R M)
      (ι R M m) ∈ globalDegree R M 1 :=
  (globalEquiv_mem_degree_iff R M 1 _).mpr (ι_mem_grading_one R M m)

end KltDP.Geometry.AffineSymmetricAlgebraSheaf
