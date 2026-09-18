import KltDP.Geometry.KltResolutionPicardCohomologyInvariants
import KltDP.Geometry.SquareZeroCompletePencilMorphismEulerOne

/-! The original minimal resolution has chi(O)=1 by its proved native
invariants. Thus an original nef square-zero divisor with K.F=-2 defines
an actual pencil on that same resolution, without assuming rationality. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.IsMinimalResolution

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

/-- The actual original divisor gives an original morphism to P1 over k
and the actual O(1) pullback. Euler characteristic one is derived from
the original klt del Pezzo resolution. -/
theorem exists_completePencilMorphism_of_nef_squareZero_of_kltDelPezzo
    (hmin : IsMinimalResolution S X π) (hDP : IsKltDelPezzo X)
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
      g ≫ projectiveSpaceToSpec k 1 = S.structureMorphism ∧
      Nonempty ((pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
          cartierDivisorModule S.toScheme F) := by
  have hchi :=
    (hmin.picard_and_structure_invariants_of_kltDelPezzo hDP hrank p hp).2.2.1
  exact S.exists_completePencilMorphism_of_nef_squareZero_of_euler_one
    hmin.regular K eK hchi F hF hFF hKF

end KltDP.Geometry.IsMinimalResolution

#check @KltDP.Geometry.IsMinimalResolution.exists_completePencilMorphism_of_nef_squareZero_of_kltDelPezzo
#print axioms KltDP.Geometry.IsMinimalResolution.exists_completePencilMorphism_of_nef_squareZero_of_kltDelPezzo
