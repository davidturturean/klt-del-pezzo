import KltDP.Geometry.AffineFiniteType
import KltDP.Geometry.ProjectiveCoordinateSectionBasicOpen
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Actual affine generators on a finite cover of a projective subscheme

An original finite morphism followed by an original closed projective
embedding has affine inverse images of the standard coordinate charts.
Their section rings are finitely generated over the original field,
with the scalar map induced by the original composite structure morphism.
The polynomial surjections evaluate at actual chart sections.

No integral, nonempty, normal, or algebraically closed hypothesis is used.
The global projective embedding is a separate construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.FiniteProjectiveChartGenerators

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

open ProjectiveChart ProjectiveCoordinateSectionBasicOpen

variable {k : Type u} [Field k] {n : ℕ} {Y Z : Scheme.{u}}
  (π : Z ⟶ Y) (i : Y ⟶ projectiveSpace k n)

/-- The literal inverse image of an original projective coordinate chart. -/
abbrev chartOpen (j : Fin (n + 1)) : Z.Opens :=
  (π ≫ i) ⁻¹ᵁ standardOpen k n j

/-- The original structure morphism of the finite cover. -/
abbrev structureMap : Z ⟶ Spec (CommRingCat.of k) :=
  π ≫ i ≫ projectiveSpaceToSpec k n

variable [IsFinite π] [IsClosedImmersion i]

/-- Finiteness supplies affineness of each actual preimage chart. -/
theorem chartOpen_isAffine (j : Fin (n + 1)) : IsAffineOpen (chartOpen π i j) :=
  (Proj.isAffineOpen_basicOpen (grading k n) (MvPolynomial.X j)
    (coordinate_mem k n j) Nat.one_pos).preimage (π ≫ i)

/-- The original composite to the field is locally of finite type. -/
theorem structureMap_locallyOfFiniteType : LocallyOfFiniteType (structureMap π i) := by
  letI : LocallyOfFiniteType (projectiveSpaceToSpec k n) :=
    projectiveSpaceToSpec_locallyOfFiniteType k n
  infer_instance

/-- The exact coefficient map to the actual preimage chart ring. -/
def chartScalars (j : Fin (n + 1)) : k →+* Γ(Z, chartOpen π i j) :=
  (baseToAffineSectionsMap (structureMap π i) (chartOpen_isAffine π i j)).hom

/-- Its spectrum is the original affine chart inclusion followed by the
original structure morphism. -/
@[reassoc]
theorem spec_map_chartScalars (j : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom (chartScalars π i j)) =
      (chartOpen_isAffine π i j).fromSpec ≫ structureMap π i :=
  Spec_map_baseToAffineSectionsMap (structureMap π i) (chartOpen_isAffine π i j)

/-- Finite type is asserted for that exact original scalar homomorphism. -/
theorem chartScalars_finiteType (j : Fin (n + 1)) :
    (chartScalars π i j).FiniteType := by
  letI : LocallyOfFiniteType (structureMap π i) := structureMap_locallyOfFiniteType π i
  exact baseToAffineSectionsMap_finiteType (structureMap π i) (chartOpen_isAffine π i j)

/-- Finitely many actual chart sections generate the actual ring over the
original field; the displayed evaluation homomorphism is surjective. -/
theorem exists_chart_generators (j : Fin (n + 1)) :
    ∃ (r : ℕ) (b : Fin r → Γ(Z, chartOpen π i j)),
      Function.Surjective (MvPolynomial.eval₂Hom (chartScalars π i j) b) := by
  letI := (chartScalars π i j).toAlgebra
  have hfinite : Algebra.FiniteType k Γ(Z, chartOpen π i j) := chartScalars_finiteType π i j
  obtain ⟨r, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hfinite
  refine ⟨r, fun a => φ (MvPolynomial.X a), ?_⟩
  have heval : MvPolynomial.eval₂Hom (chartScalars π i j)
      (fun a => φ (MvPolynomial.X a)) = φ.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [MvPolynomial.eval₂Hom_C]
      change chartScalars π i j c = φ (MvPolynomial.C c)
      exact (φ.commutes c).symm
    · intro a
      exact MvPolynomial.eval₂Hom_X' _ _ a
  rw [heval]
  exact hφ

end KltDP.Geometry.FiniteProjectiveChartGenerators
