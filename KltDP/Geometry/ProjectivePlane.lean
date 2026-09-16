import KltDP.Compatibility.PolynomialDimension
import KltDP.Geometry.ProjectiveSpaceDimension

/-!
# An actual normal projective plane

The polynomial dimension theorem is proved at the existing Mathlib pin.
Applying it to the actual projective-chart topology adapters gives the
dimension of projective space, and hence a concrete normal projective
surface over every field. No dimension or existence premise is required.
-/

noncomputable section

universe u

namespace KltDP.Geometry

/-- The existing `Proj` construction of projective `n`-space has actual
topological Krull dimension `n`. -/
theorem projectiveSpace_topologicalKrullDim (k : Type u) [Field k] (n : ℕ) :
    topologicalKrullDim (projectiveSpace k n) = (n : WithBot ℕ∞) :=
  projectiveSpace_topologicalKrullDim_of_polynomial_dimension k n
    (KltDP.Compatibility.polynomial_ringKrullDim k n)

/-- The actual projective plane with its existing structure morphism,
integral scheme, integrally closed domain stalks, and dimension two. -/
def projectivePlaneSurface (k : Type u) [Field k] : NormalProjectiveSurface k :=
  projectivePlaneSurfaceOfPolynomialDimension k
    (KltDP.Compatibility.polynomial_ringKrullDim k 2)

/-- Normal projective surfaces over a field have an actual witness. -/
theorem normalProjectiveSurface_nonempty (k : Type u) [Field k] :
    Nonempty (NormalProjectiveSurface k) :=
  ⟨projectivePlaneSurface k⟩

@[simp] theorem projectivePlaneSurface_toScheme (k : Type u) [Field k] :
    (projectivePlaneSurface k).toScheme = projectiveSpace k 2 := rfl

@[simp] theorem projectivePlaneSurface_structureMorphism (k : Type u) [Field k] :
    (projectivePlaneSurface k).structureMorphism = projectiveSpaceToSpec k 2 := rfl

end KltDP.Geometry
