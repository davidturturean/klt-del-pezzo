import KltDP.Compatibility.ProjProper
import KltDP.Geometry.ProjectiveFiniteType

/-!
# Properness from an actual projective embedding

The degree-zero subring of the homogeneous polynomial ring is identified with
its coefficient field by an explicit ring equivalence. Finite generation of
the polynomial ring then supplies the hypothesis of the imported valuative
properness proof. Finally, the defining closed projective embedding yields
properness by composition. The surface definition is unchanged.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The constants ring homomorphism is an isomorphism in `CommRingCat`. -/
instance projectiveSpaceConstants_isIso (k : Type u) [Field k] (n : ℕ) :
    IsIso (CommRingCat.ofHom (projectiveSpaceConstants k n)) := by
  let e := (projectiveSpaceZeroRingEquiv k n).toCommRingCatIso
  have he : e.hom = CommRingCat.ofHom (projectiveSpaceConstants k n) := by
    ext a
    rfl
  rw [← he]
  infer_instance

/-- The canonical morphism from polynomial projective space to its field is
proper. Polynomial finite generation supplies the general Proj hypothesis. -/
instance projectiveSpaceToSpec_isProper (k : Type u) [Field k] (n : ℕ) :
    IsProper (projectiveSpaceToSpec k n) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k
  letI : Algebra.FiniteType k (MvPolynomial (Fin (n + 1)) k) :=
    Algebra.FiniteType.mvPolynomial k (Fin (n + 1))
  letI : IsScalarTower k (𝒜 0) (MvPolynomial (Fin (n + 1)) k) :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := 𝒜 0)
      (A := MvPolynomial (Fin (n + 1)) k) (fun _ ↦ rfl)
  letI : Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin (n + 1)) k) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (𝒜 0) _
  change IsProper (Proj.toSpecZero 𝒜 ≫
    Spec.map (CommRingCat.ofHom (projectiveSpaceConstants k n)))
  infer_instance

/-- A closed projective embedding proves properness of the original morphism. -/
theorem IsProjectiveOverField.isProper {k : Type u} [Field k]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    (hf : IsProjectiveOverField f) : IsProper f := by
  obtain ⟨n, i, hi, hfactor⟩ := hf
  letI : IsClosedImmersion i := hi
  rw [← hfactor]
  infer_instance

/-- Properness is derived from a normal projective surface's existing embedding. -/
instance NormalProjectiveSurface.isProper_structureMorphism
    {k : Type u} [Field k] (X : NormalProjectiveSurface k) :
    IsProper X.structureMorphism :=
  X.projective.isProper

end KltDP.Geometry
