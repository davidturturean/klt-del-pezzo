import KltDP.Geometry.KltResolutionSquareZeroPencilSurjective
import KltDP.Geometry.KltSquareZeroPencilStein

/-! The original nef square-zero divisor produces an actual pencil with
geometrically connected scheme fibers. The map is constructed here from
the divisor; neither a pencil nor its connectedness is supplied as data.
This does not assert smoothness or geometric integrality of the generic
fiber, which are separate obligations in the ruling construction. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.IsMinimalResolution

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {ρ : S.toScheme ⟶ X.toScheme}

/-- A nef square-zero divisor of canonical degree -2 on the original
resolution defines a proper surjective pencil with connected fibers
after every field-valued base change. -/
theorem exists_geometricallyConnectedPencil_of_nef_squareZero_of_kltDelPezzo
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
      g ≫ projectiveSpaceToSpec k 1 = S.structureMorphism ∧
      IsProper g ∧ Surjective g ∧ IsIso g.c ∧
      Nonempty ((pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
          cartierDivisorModule S.toScheme F) ∧
      ∀ (l : Type u) [Field l] (q : Spec (CommRingCat.of l) ⟶ projectiveSpace k 1),
        ConnectedSpace (pullback g q : Scheme.{u}) := by
  obtain ⟨g, hg, hproper, _hgeneric, _hdominant, hsurj, ⟨e⟩⟩ :=
    hmin.exists_surjective_completePencilMorphism_of_nef_squareZero_of_kltDelPezzo
      hDP hrank p hp K eK F hF hFF hKF
  letI : IsProper g := hproper
  letI : Surjective g := hsurj
  obtain ⟨hiso, hconnected⟩ :=
    KltSquareZeroPencilStein.structureSheaf_iso_and_geometrically_connected
      ρ hmin hDP hrank p hp K eK F hFF hKF g hg e
  exact ⟨g, hg, hproper, hsurj, hiso, ⟨e⟩, hconnected⟩

end KltDP.Geometry.IsMinimalResolution

#check @KltDP.Geometry.IsMinimalResolution.exists_geometricallyConnectedPencil_of_nef_squareZero_of_kltDelPezzo
#print axioms KltDP.Geometry.IsMinimalResolution.exists_geometricallyConnectedPencil_of_nef_squareZero_of_kltDelPezzo
