import KltDP.Geometry.RationalTreePicardIntrinsicNode
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Finiteness for the original native stalk Kähler module

The given scheme structure morphism determines both the affine section
algebra and the stalk algebra. Their actual germ is the localization map;
finite type of the affine algebra therefore gives essential finite type
of that same stalk algebra and finiteness of its Kähler module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.StalkKaehlerFiniteness

open IntrinsicNodal

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))

/-- The original affine germ preserves the two algebras defined by f. -/
theorem affine_stalk_scalarTower {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) :
    letI := affineSectionsAlgebra f hU
    letI := stalkAlgebra f x
    letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := by
  letI := affineSectionsAlgebra f hU
  letI := stalkAlgebra f x
  letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  apply IsScalarTower.of_algebraMap_eq'
  exact congrArg (fun g : CommRingCat.of k ⟶ X.presheaf.stalk x => g.hom)
    (baseToAffineSectionsMap_germ f hU x hx).symm

/-- A stalk of a locally finite-type scheme uses an essentially finite-type
algebra for its original structure morphism. -/
theorem stalk_essFiniteType [LocallyOfFiniteType f] (x : X) :
    letI := stalkAlgebra f x
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  let U : X.Opens := (X.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.map x)
  have hx : x ∈ U := X.affineCover.covers x
  letI := stalkAlgebra f x
  letI := affineSectionsAlgebra f hU
  letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  letI := affine_stalk_scalarTower f hU x hx
  letI : Algebra.FiniteType k Γ(X, U) := affineSectionsAlgebra_finiteType f hU
  letI := hU.isLocalization_stalk ⟨x, hx⟩
  letI : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  exact Algebra.EssFiniteType.comp k Γ(X, U) (X.presheaf.stalk x)

/-- Finiteness is for the native Kähler module with the original stalk scalars. -/
theorem stalk_kaehler_finite [LocallyOfFiniteType f] (x : X) :
    letI := stalkAlgebra f x
    Module.Finite (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) := by
  letI := stalkAlgebra f x
  letI := stalk_essFiniteType f x
  infer_instance

end KltDP.Geometry.StalkKaehlerFiniteness
