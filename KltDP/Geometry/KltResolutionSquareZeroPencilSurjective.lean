import KltDP.Geometry.KltResolutionSquareZeroPencilMorphism
import KltDP.Geometry.SquareZeroPencilSurjectiveEulerOne

/-! An original nef square-zero divisor on the original klt resolution
defines an actual proper surjective pencil. The original map, its field
triangle and its O(1) pullback are retained throughout. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.IsMinimalResolution

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {ρ : S.toScheme ⟶ X.toScheme}

local instance kltSurjectivePencilTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- The actual original resolution supplies a proper surjective pencil;
no rationality, Euler value, pencil or map property is an input. -/
theorem exists_surjective_completePencilMorphism_of_nef_squareZero_of_kltDelPezzo
    (hmin : IsMinimalResolution S X ρ) (hDP : IsKltDelPezzo X)
    (hrank : X.picardRank = 1) (p : ℕ) [CharP k p] (hp : 0 < p)
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (F : CartierDivisor S.toScheme)
    (hF : Positivity.IsNef S.structureMorphism
      (cartierDivisorInvertibleSheaf S.toScheme F))
    (hFF : S.intersectionPairing hmin.regular F F = 0)
    (hKF : S.intersectionPairing hmin.regular K F = -2) :
    ∃ g : S.toScheme ⟶ projectiveSpace k 1,
      g ≫ projectiveSpaceToSpec k 1 = S.structureMorphism ∧ IsProper g ∧
      GenericPointPreserving g ∧ IsDominant g ∧ Surjective g ∧
      Nonempty ((pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
          cartierDivisorModule S.toScheme F) := by
  obtain ⟨g, hg, ⟨e⟩⟩ :=
    hmin.exists_completePencilMorphism_of_nef_squareZero_of_kltDelPezzo
      hDP hrank p hp K eK F hF hFF hKF
  have hchi :=
    (hmin.picard_and_structure_invariants_of_kltDelPezzo hDP hrank p hp).2.2.1
  obtain ⟨hproper, hgeneric, hdominant, hsurjective⟩ :=
    S.squareZero_completePencilMorphism_properties_of_euler_one
      hmin.regular K eK hchi F hF hFF hKF g hg e
  exact ⟨g, hg, hproper, hgeneric, hdominant, hsurjective, ⟨e⟩⟩

end KltDP.Geometry.IsMinimalResolution

#check @KltDP.Geometry.IsMinimalResolution.exists_surjective_completePencilMorphism_of_nef_squareZero_of_kltDelPezzo
#print axioms KltDP.Geometry.IsMinimalResolution.exists_surjective_completePencilMorphism_of_nef_squareZero_of_kltDelPezzo
