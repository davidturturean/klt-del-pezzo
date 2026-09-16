import KltDP.Geometry.Surface
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Finite type of the actual projective structure map

The homogeneous affine charts of `Proj A` have coordinate rings `(A_f)₀`.
Their morphisms to `Spec A₀` are the spectra of the actual degree-zero
inclusion maps. This compatibility, supplied by `Proj.awayι_toSpecZero`,
allows the ring-theoretic finite-type theorem to be glued on the source.

For projective space, the degree-zero ring is identified with the base field
by the existing constant-polynomial map. The conclusion then passes to any
actual closed projective embedding over that field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- A finitely generated graded algebra over its degree-zero ring has a
structure morphism locally of finite type, via its actual homogeneous charts. -/
theorem proj_toSpecZero_locallyOfFiniteType {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [Algebra.FiniteType (𝒜 0) A] : LocallyOfFiniteType (Proj.toSpecZero 𝒜) := by
  apply IsLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (Proj.affineOpenCover 𝒜).openCover
  intro i
  change LocallyOfFiniteType
    (Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2 ≫ Proj.toSpecZero 𝒜)
  rw [Proj.awayι_toSpecZero]
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  change Algebra.FiniteType (𝒜 0) (HomogeneousLocalization.Away 𝒜 (i.2 : A))
  exact HomogeneousLocalization.Away.finiteType (𝒜 := 𝒜)
    (i.2 : A) (i.1 : ℕ) i.2.2

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every degree-zero homogeneous polynomial is a constant polynomial. -/
theorem projectiveSpaceConstants_surjective (k : Type u) [Field k] (n : ℕ) :
    Function.Surjective (projectiveSpaceConstants k n) := by
  intro p
  have hhom : MvPolynomial.IsHomogeneous p.1 0 := p.2
  have hdegree : p.1.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (n + 1))).mpr hhom
  refine ⟨p.1.coeff 0, ?_⟩
  apply Subtype.ext
  exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree).symm

/-- The constant-polynomial map identifies the degree-zero ring with the
actual base field, without choosing a different algebra structure. -/
theorem projectiveSpaceConstants_bijective (k : Type u) [Field k] (n : ℕ) :
    Function.Bijective (projectiveSpaceConstants k n) := by
  refine ⟨?_, projectiveSpaceConstants_surjective k n⟩
  intro a b hab
  apply MvPolynomial.C_injective (Fin (n + 1)) k
  exact congrArg Subtype.val hab

/-- The degree-zero coordinate ring of projective space, as an actual ring
isomorphism induced by constants. -/
def projectiveSpaceZeroRingEquiv (k : Type u) [Field k] (n : ℕ) :
    k ≃+* MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0 :=
  RingEquiv.ofBijective (projectiveSpaceConstants k n)
    (projectiveSpaceConstants_bijective k n)

/-- The actual projective-space structure map is locally of finite type. -/
theorem projectiveSpaceToSpec_locallyOfFiniteType (k : Type u) [Field k] (n : ℕ) :
    LocallyOfFiniteType (projectiveSpaceToSpec k n) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k
  letI : Algebra.FiniteType k (MvPolynomial (Fin (n + 1)) k) :=
    Algebra.FiniteType.mvPolynomial k (Fin (n + 1))
  letI : IsScalarTower k (𝒜 0) (MvPolynomial (Fin (n + 1)) k) :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := 𝒜 0)
      (A := MvPolynomial (Fin (n + 1)) k) (fun _ ↦ rfl)
  letI : Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin (n + 1)) k) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (𝒜 0) _
  letI : LocallyOfFiniteType (Proj.toSpecZero 𝒜) :=
    proj_toSpecZero_locallyOfFiniteType 𝒜
  letI : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (projectiveSpaceConstants k n))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.FiniteType.of_surjective _ (projectiveSpaceConstants_surjective k n))
  change LocallyOfFiniteType
    (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (projectiveSpaceConstants k n)))
  infer_instance

/-- Finite type follows from the defining closed projective embedding and
its compatibility with the given base structure morphism. -/
theorem IsProjectiveOverField.locallyOfFiniteType {k : Type u} [Field k]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    (hf : IsProjectiveOverField f) : LocallyOfFiniteType f := by
  obtain ⟨n, i, hi, hfactor⟩ := hf
  letI : IsClosedImmersion i := hi
  letI : LocallyOfFiniteType (projectiveSpaceToSpec k n) :=
    projectiveSpaceToSpec_locallyOfFiniteType k n
  rw [← hfactor]
  infer_instance

/-- Quasi-compactness supplies the second part of the usual finite-type
condition, with no finiteness assumption added to the source scheme. -/
theorem IsProjectiveOverField.quasiCompact {k : Type u} [Field k]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    (hf : IsProjectiveOverField f) : QuasiCompact f := by
  letI : NoetherianSpace X := hf.noetherianSpace
  infer_instance

/-- Projective schemes over fields are Jacobson spaces. This applies to
arbitrary points; identifying their closed points with rational points still
requires the residue-field argument. -/
theorem IsProjectiveOverField.jacobsonSpace {k : Type u} [Field k]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    (hf : IsProjectiveOverField f) : JacobsonSpace X := by
  letI : LocallyOfFiniteType f := hf.locallyOfFiniteType
  exact LocallyOfFiniteType.jacobsonSpace f

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

instance : LocallyOfFiniteType X.structureMorphism := X.projective.locallyOfFiniteType

instance : JacobsonSpace X.toScheme := X.projective.jacobsonSpace

end NormalProjectiveSurface

end KltDP.Geometry
