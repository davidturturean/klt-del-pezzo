import KltDP.Geometry.AffineSpecMapReflection
import KltDP.Geometry.TensorFiberProjectionIso
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Original fiber projections determine the original residue tensor
scalar map. Ring-map comparison and dimension are proved outside Spec. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

namespace KltDP.Geometry.AffineFiberScalarRank

/-- An actual chart pullback square transports the actual field fiber. -/
theorem isIso_snd_of_chart_square
    {A B X Y K : Scheme.{u}} (a : A ⟶ X) (g : A ⟶ B)
    (π : X ⟶ Y) (c : B ⟶ Y) (H : IsPullback a g π c)
    (i : K ⟶ B) [IsIso (pullback.snd π (i ≫ c))] :
    IsIso (pullback.snd g i) := by
  have hp := (IsPullback.of_hasPullback g i).paste_horiz H
  rw [← hp.isoPullback_hom_snd]
  infer_instance

/-- Identify the original tensor scalar map as a ring map, without
applying the concrete Spec construction to this equality. -/
theorem algebraMap_eq_includeLeft (R A K : Type u)
    [CommRing R] [CommRing A] [Field K] [Algebra R A] [Algebra R K] :
    algebraMap K (K ⊗[R] A) =
      (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[R] A) := by
  ext x
  rfl

/-- The original fiber being a point makes its original scalar map bijective. -/
theorem algebraMap_bijective_of_isIso_snd
    (R A K : Type u) [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra R K]
    [IsIso (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    Function.Bijective (algebraMap K (K ⊗[R] A)) := by
  letI := TensorFiberProjectionIso.includeLeft_spec_isIso R A K
  rw [algebraMap_eq_includeLeft R A K]
  exact AffineSpecMapReflection.bijective_of_isIso_spec
    (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[R] A))

/-- A bijective original algebra map identifies its vector space with the field. -/
theorem finrank_eq_one_of_algebraMap_bijective
    (K B : Type u) [Field K] [CommRing B] [Algebra K B]
    (h : Function.Bijective (algebraMap K B)) : Module.finrank K B = 1 := by
  have hb : Function.Bijective (Algebra.linearMap K B) := h
  rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]

/-- The original residue tensor has precisely the dimension required by
finite-algebra Nakayama. -/
theorem finrank_eq_one_of_isIso_snd
    (R A K : Type u) [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra R K]
    [IsIso (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    Module.finrank K (K ⊗[R] A) = 1 :=
  finrank_eq_one_of_algebraMap_bijective K (K ⊗[R] A)
    (algebraMap_bijective_of_isIso_snd R A K)

#check KltDP.Geometry.AffineFiberScalarRank.finrank_eq_one_of_isIso_snd
#print axioms KltDP.Geometry.AffineFiberScalarRank.algebraMap_eq_includeLeft
#print axioms KltDP.Geometry.AffineFiberScalarRank.algebraMap_bijective_of_isIso_snd
#print axioms KltDP.Geometry.AffineFiberScalarRank.finrank_eq_one_of_isIso_snd

end KltDP.Geometry.AffineFiberScalarRank
