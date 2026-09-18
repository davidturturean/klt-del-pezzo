import KltDP.Geometry.AffineChartCoefficientTransport
import KltDP.Geometry.QuadraticRootGlobalIdealRegular

/-!
# The original global-cover root equation squares to the pulled branch equation

The actual original chart map sends a base coefficient to its original
quadratic algebra image. The defining root-square relation therefore
holds in sections on the actual image affine open of the global cover,
with the original scheme morphism's appLE map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open QuadraticCover TransitionUnitGluing PrincipalQuotientOpenChart

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- Each original equation chart lies over its original base affine chart. -/
theorem rootEquationOpen_le_preimage (i : ι) :
    (D.rootEquationOpen i).1 ≤ D.morphism ⁻¹ᵁ D.opens i := by
  rintro x ⟨z, hz, rfl⟩
  exact (D.range_chartι i).le ⟨z, rfl⟩

/-- The literal pullback of the original branch coefficient is the square of the actual root section. -/
theorem rootEquationSection_square (i : ι) :
    D.morphism.appLE (D.opens i) (D.rootEquationOpen i).1
        (D.rootEquationOpen_le_preimage i) (D.sections i) =
      D.rootEquationSection i ^ 2 := by
  let s := res X (le_refl (D.opens i)) (D.sections i)
  have hs : algebraMap Γ(X, D.opens i) (CoverAlgebra s) (D.sections i) = root s ^ 2 :=
    (congrArg (algebraMap Γ(X, D.opens i) (CoverAlgebra s))
      (res_self X (D.opens i) (D.sections i)).symm).trans (root_sq s).symm
  calc
    _ = sectionEquiv (D.chartι i)
        (algebraMap Γ(X, D.opens i) (CoverAlgebra s) (D.sections i)) :=
      appLE_coefficient D.morphism ⟨D.opens i, D.affine i⟩ (D.chartι i)
        (algebraMap Γ(X, D.opens i) (CoverAlgebra s)) (D.chartι_morphism i)
        (D.rootEquationOpen_le_preimage i) (D.sections i)
    _ = sectionEquiv (D.chartι i) (root s ^ 2) := congrArg (sectionEquiv (D.chartι i)) hs
    _ = D.rootEquationSection i ^ 2 := map_pow (sectionEquiv (D.chartι i)) (root s) 2

end KltDP.Geometry.QuadraticCoverAtlas.Data

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.rootEquationSection_square
