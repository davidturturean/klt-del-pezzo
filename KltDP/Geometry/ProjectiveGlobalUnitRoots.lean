import KltDP.Geometry.ProperGlobalUnitRoots
import KltDP.Geometry.ProjectiveProper
import KltDP.Geometry.ProjectiveSpaceIntegral

/-!
# Unit roots on the actual projective-space scheme

This specializes the global-section root construction to the existing Proj
scheme and its original structure morphism. Properness and integrality are
derived by the imported projective-space proofs. The case of the projective
line supplies the branch-unit root step on an actually trivialized rational
component; it does not assert triviality of its line bundle.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- Every actual invertible global section on projective space has a unit root. -/
theorem projectiveSpace_exists_global_unit_pow (d : ℕ)
    (b : Γ(projectiveSpace k d, ⊤)ˣ) (n : ℕ) (hn : 0 < n) :
    ∃ r : Γ(projectiveSpace k d, ⊤)ˣ, r ^ n = b := by
  letI : IsIntegral (projectiveSpace k d) := projectiveSpace_isIntegral k d
  letI : LocallyOfFiniteType (projectiveSpaceToSpec k d) :=
    projectiveSpaceToSpec_locallyOfFiniteType k d
  exact ⟨ProperGlobalUnitRoots.globalUnitRoot (projectiveSpaceToSpec k d) b n hn,
    ProperGlobalUnitRoots.globalUnitRoot_pow (projectiveSpaceToSpec k d) b n hn⟩

/-- In particular, the square map is surjective on actual global units of P1. -/
theorem projectiveLine_global_units_square_surjective :
    Function.Surjective (fun r : Γ(projectiveSpace k 1, ⊤)ˣ => r ^ 2) := by
  intro b
  exact projectiveSpace_exists_global_unit_pow k 1 b 2 (by decide)

end KltDP.Geometry
