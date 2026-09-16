/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Compatibility.GradedProjIso
import KltDP.Compatibility.SymmetricAlgebra.BasisGrading
import KltDP.Geometry.SymmetricProjectiveSpectrumZero
import KltDP.Geometry.Surface

/-!
# Actual symmetric Proj and the existing projective-space scheme

The basis algebra equivalence, with its proved intrinsic degree comparison,
induces an isomorphism from the actual symmetric Proj to the existing
polynomial projective space. Its original degree-zero constants give the
original morphism to Spec k, and that morphism commutes with the isomorphism.

Finite positive-dimensional field modules therefore give actual projective
schemes. A closed immersion from a nonempty scheme into such a symmetric Proj
also forces positive module dimension, using the separate actual rank-zero
calculation. No projective-bundle identification, raw literature statement,
stage-projectivity conclusion or equivalent witness is assumed or admitted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SymmetricProjectiveSpace

open KltDP.SymmetricAlgebra

variable (k M : Type u) [Field k] [AddCommGroup M] [Module k M]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original coefficient map into symmetric degree zero. -/
def constants : k →+* grading k M 0 where
  toFun a := ⟨algebraMap k (KltDP.SymmetricAlgebra k M) a, Submodule.algebraMap_mem a⟩
  map_one' := Subtype.ext (map_one (algebraMap k (KltDP.SymmetricAlgebra k M)))
  map_zero' := Subtype.ext (map_zero (algebraMap k (KltDP.SymmetricAlgebra k M)))
  map_mul' a b := Subtype.ext (map_mul (algebraMap k (KltDP.SymmetricAlgebra k M)) a b)
  map_add' a b := Subtype.ext (map_add (algebraMap k (KltDP.SymmetricAlgebra k M)) a b)

/-- The actual symmetric Proj structure map to the original field. -/
def structureMap : Proj (grading k M) ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (grading k M) ≫ Spec.map (CommRingCat.ofHom (constants k M))

variable {k M} {n : ℕ}

/-- The actual graded equivalence gives an isomorphism to the existing
projective-space scheme, for a basis with `n+1` elements. -/
def basisIso (b : Basis (Fin (n + 1)) k M) :
    Proj (grading k M) ≅ projectiveSpace k n :=
  GradedProjIso.iso (𝒜 := grading k M)
    (ℬ := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
    (equivMvPolynomial b).toRingEquiv
    (fun i x => (equivMvPolynomial_mem_homogeneous_iff b i x).symm)

/-- The comparison preserves the original structure maps, including the
actual degree-zero coefficient maps. -/
theorem basisIso_structure (b : Basis (Fin (n + 1)) k M) :
    (basisIso b).hom ≫ projectiveSpaceToSpec k n = structureMap k M := by
  apply GradedProjIso.iso_hom_comp_toSpecBase
    (e := (equivMvPolynomial b).toRingEquiv)
    (he := fun i x => (equivMvPolynomial_mem_homogeneous_iff b i x).symm)
    (constants k M) (projectiveSpaceConstants k n)
  apply RingHom.ext
  intro a
  apply Subtype.ext
  change (equivMvPolynomial b).symm (MvPolynomial.C a) =
    algebraMap k (KltDP.SymmetricAlgebra k M) a
  exact (equivMvPolynomial b).symm.commutes a

/-- Projectivity is provided by the displayed actual scheme isomorphism. -/
theorem structureMap_isProjective_of_basis (b : Basis (Fin (n + 1)) k M) :
    IsProjectiveOverField (structureMap k M) :=
  ⟨n, (basisIso b).hom, inferInstance, basisIso_structure b⟩

variable (k M)

/-- The actual symmetric Proj of a finite nonzero vector space is projective
over the original field. The positivity needed for `r-1` is proved first. -/
theorem structureMap_isProjective [Module.Finite k M] [Nontrivial M] :
    IsProjectiveOverField (structureMap k M) := by
  let n := Module.finrank k M - 1
  have hn : Module.finrank k M = n + 1 := by
    dsimp only [n]
    exact (Nat.sub_add_cancel (Nat.succ_le_of_lt (Module.finrank_pos (R := k) (M := M)))).symm
  exact structureMap_isProjective_of_basis (Module.finBasisOfFinrankEq k M hn)

variable {k M}

/-- A genuine closed immersion into the actual symmetric Proj of a finite
field module gives the existing projectivity predicate. Nonemptiness excludes
the actual empty rank-zero target; no positive-rank premise is inserted. -/
theorem projective_of_closedImmersion [Module.Finite k M]
    {X : Scheme.{u}} [Nonempty X] (f : X ⟶ Proj (grading k M)) [IsClosedImmersion f] :
    IsProjectiveOverField (f ≫ structureMap k M) := by
  letI : Nontrivial M := KltDP.SymmetricAlgebra.nontrivial_of_morphism f
  obtain ⟨n, i, hi, hstructure⟩ := structureMap_isProjective k M
  letI : IsClosedImmersion i := hi
  exact ⟨n, f ≫ i, inferInstance, by rw [Category.assoc, hstructure]⟩

end KltDP.Geometry.SymmetricProjectiveSpace
