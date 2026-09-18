import KltDP.Geometry.SmoothSurfaceKaehlerAtlas
import KltDP.Geometry.KaehlerLocalizedFrame
import KltDP.Geometry.StalkKaehlerFiniteness

/-!
# A native Kähler basis at an actual smooth surface stalk

Localize the existing standard-smooth chart frame at the given point,
using the original germ and the proved original stalk scalar tower.
The determinant equivalence evaluates its exact basis wedge to one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SmoothSurfaceStalkKaehlerBasis

open IntrinsicNodal SmoothSurfaceKaehlerAtlas

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [hSmooth : IsSmoothOfRelativeDimension 2 f]

include hSmooth

/-- An actual smooth chart supplies a native basis at every original stalk. -/
def basis (x : X) :
    letI := stalkAlgebra f x
    Basis (Fin 2) (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) := by
  let U : X.Opens := atlasOpen f x
  let hU : IsAffineOpen U := atlasOpen_isAffineOpen f x
  have hx : x ∈ U := atlasOpen_mem f x
  letI := affineSectionsAlgebra f hU
  letI := stalkAlgebra f x
  letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  letI := StalkKaehlerFiniteness.affine_stalk_scalarTower f hU x hx
  letI := hU.isLocalization_stalk ⟨x, hx⟩
  exact KaehlerLocalizedFrame.localizedFrame k Γ(X, U) (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (atlasFrame f x)

/-- A genuine scalar determinant evaluator on the same native top exterior power. -/
def determinant (x : X) :
    letI := stalkAlgebra f x
    (⋀[(X.presheaf.stalk x)]^2 (KaehlerDifferential k (X.presheaf.stalk x))) ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x := by
  letI := stalkAlgebra f x
  exact AffineTopDifferentialFrame.determinantEquiv (basis f x)

/-- The original native basis wedge has scalar coordinate one. -/
theorem determinant_basis_wedge (x : X) :
    letI := stalkAlgebra f x
    determinant f x (exteriorPower.ιMulti (X.presheaf.stalk x) 2 (basis f x)) = 1 := by
  letI := stalkAlgebra f x
  exact AffineTopDifferentialFrame.determinantEquiv_basis_wedge (basis f x)

end KltDP.Geometry.SmoothSurfaceStalkKaehlerBasis
