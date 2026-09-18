/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Compatibility.GradedProjIso
import KltDP.Compatibility.SymmetricAlgebra.BasisGrading
import KltDP.Geometry.RelativeProjectiveBasicOpenBaseChange

/-!
# Actual symmetric Proj in an original basis over a commutative ring

The intrinsic symmetric quotient and grading are unchanged. An actual basis
produces the polynomial Proj comparison by the existing homogeneous-localization
construction. The degree-zero coefficient map is retained, over any original
commutative base ring. No geometric chart or projective-bundle witness is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.RelativeSymmetricProj

open KltDP.SymmetricAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra

variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

abbrev scheme : Scheme := Proj (grading R M)

/-- Original coefficients in degree zero of the intrinsic symmetric algebra. -/
def constants : R →+* grading R M 0 where
  toFun a := ⟨algebraMap R (KltDP.SymmetricAlgebra R M) a, Submodule.algebraMap_mem a⟩
  map_one' := Subtype.ext (map_one (algebraMap R (KltDP.SymmetricAlgebra R M)))
  map_zero' := Subtype.ext (map_zero (algebraMap R (KltDP.SymmetricAlgebra R M)))
  map_mul' a b := Subtype.ext (map_mul (algebraMap R (KltDP.SymmetricAlgebra R M)) a b)
  map_add' a b := Subtype.ext (map_add (algebraMap R (KltDP.SymmetricAlgebra R M)) a b)

/-- The actual symmetric Proj morphism to its original base. -/
def toBase : scheme R M ⟶ Spec (.of R) :=
  Proj.toSpecZero (grading R M) ≫ Spec.map (CommRingCat.ofHom (constants R M))

variable {R M} {n : ℕ}

/-- Actual free projective coordinates supplied by an actual basis. -/
def basisIso (b : Basis (Fin (n + 1)) R M) :
    scheme R M ≅ RelativeProjectiveChart.freeProjectivization R n :=
  GradedProjIso.iso (𝒜 := grading R M)
    (ℬ := RelativeProjectiveChart.grading R n)
    (equivMvPolynomial b).toRingEquiv
    (fun i x => (equivMvPolynomial_mem_homogeneous_iff b i x).symm)

/-- The basis comparison preserves the literal degree-zero/base diagram. -/
@[reassoc] theorem basisIso_toBase (b : Basis (Fin (n + 1)) R M) :
    (basisIso b).hom ≫ RelativeProjectiveChart.freeProjectivizationToBase R n =
      toBase R M := by
  apply GradedProjIso.iso_hom_comp_toSpecBase
    (e := (equivMvPolynomial b).toRingEquiv)
    (he := fun i x => (equivMvPolynomial_mem_homogeneous_iff b i x).symm)
    (constants R M) (RelativeProjectiveChart.baseConstants R n)
  apply RingHom.ext
  intro a
  apply Subtype.ext
  change (equivMvPolynomial b).symm (MvPolynomial.C a) =
    algebraMap R (KltDP.SymmetricAlgebra R M) a
  exact (equivMvPolynomial b).symm.commutes a

@[reassoc] theorem basisIso_inv_toBase (b : Basis (Fin (n + 1)) R M) :
    (basisIso b).inv ≫ toBase R M =
      RelativeProjectiveChart.freeProjectivizationToBase R n := by
  rw [← basisIso_toBase b, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Original polynomial basic opens pull back along the actual inverse
symmetric-algebra coordinate map. -/
@[simp] theorem basisIso_preimage_basicOpen (b : Basis (Fin (n + 1)) R M)
    (p : RelativeProjectiveChart.homogeneousRing R n) :
    (basisIso b).hom ⁻¹ᵁ Proj.basicOpen (RelativeProjectiveChart.grading R n) p =
      Proj.basicOpen (grading R M) ((equivMvPolynomial b).symm p) := rfl

/-- The inverse comparison uses the original symmetric-algebra coordinate map. -/
@[simp] theorem basisIso_inv_preimage_basicOpen (b : Basis (Fin (n + 1)) R M)
    (s : KltDP.SymmetricAlgebra R M) :
    (basisIso b).inv ⁻¹ᵁ Proj.basicOpen (grading R M) s =
      Proj.basicOpen (RelativeProjectiveChart.grading R n) (equivMvPolynomial b s) := rfl

end KltDP.Geometry.RelativeSymmetricProj

#print axioms KltDP.Geometry.RelativeSymmetricProj.basisIso
#print axioms KltDP.Geometry.RelativeSymmetricProj.basisIso_toBase
