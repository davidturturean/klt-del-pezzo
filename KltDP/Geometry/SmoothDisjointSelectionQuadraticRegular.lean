import KltDP.Geometry.SmoothSelectedPrimeQuadraticSurface
import KltDP.Geometry.OriginalCartierQuadraticRegular
import KltDP.Geometry.SelectedPrimeUnionSmooth

/-!
# A regular original quadratic surface from a disjoint even selection

The actual smooth surface, nonempty even selection of actual disjoint
smooth prime curves, and integral Picard half-class produce the original
Cartier data and square-root cover. The canonical branch ideal is exactly
the vanishing ideal of the selected union; its smoothness, reducedness,
and nonemptiness are all derived. The same original cover is integral,
normal, projective, two-dimensional, finite flat and surjective over the
surface, and every one of its actual points is regular.

No cover regularity or geometry, branch-union smoothness, coordinates,
valuation, or splitting theorem is supplied as an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance smoothDisjointSelectionQuadraticRegularSeparated : S.toScheme.IsSeparated :=
  surfaceSeparated S
local instance smoothDisjointSelectionQuadraticRegularMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- A disjoint nonempty even selection of actual smooth curves gives the original regular cover. -/
theorem exists_regular_quadratic_surface_of_nonempty_disjoint_even_selection
    (N : Finset S.PrimeCurve) (hN : N.Nonempty)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D => Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hcurves : ∀ C ∈ N, IsSmooth C.toSpec)
    (m : Additive S.toScheme.Pic)
    (heven : S.smoothWeilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil N)) =
      (2 : ℕ) • m) (h2 : IsUnit (2 : k)) :
    ∃ (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
      (L : InvertibleSheaf S.toScheme)
      (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E),
      S.cartierToWeilHom E = S.selectedPrimeWeil N ∧ L.toPic = m.toMul ∧
      effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
        Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N) ∧
      let A := InvertibleQuadraticAtlas.fromSquareRoot S.toScheme L
        (cartierDivisorModule S.toScheme E) e (effectiveCartierSection S.toScheme E hE)
      IsIntegral A.scheme ∧ IsNormalScheme A.scheme ∧
        IsProjectiveOverField (A.morphism ≫ S.structureMorphism) ∧
        topologicalKrullDim A.scheme = 2 ∧ IsFinite A.morphism ∧
        AlgebraicGeometry.Flat A.morphism ∧ AlgebraicGeometry.Surjective A.morphism ∧
        ∀ y : A.scheme, RegularPoint A.scheme y := by
  obtain ⟨E, hE, L, e, hweil, hL, hIJ, hint, hnormal, hproj, hdim, hfin, hflat, hsurj⟩ :=
    S.exists_normal_projective_quadratic_cover_of_nonempty_even_selection N hN m heven h2
  let J := S.selectedPrimeUnionIdeal N
  have hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued := by
    rw [hIJ]
    exact J.glued_isReduced (Scheme.IdealSheafData.vanishingIdeal_support (I := J)).symm
  have hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued := by
    rw [hIJ]
    obtain ⟨x, hx⟩ := S.selectedPrimeClosedUnion_nonempty N hN
    exact ⟨J.gluedSupportHomeomorph.symm ⟨x, hx⟩⟩
  have hsm : IsSmooth
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism) := by
    rw [hIJ]
    exact S.selectedPrimeUnion_isSmooth N hdisj hcurves
  exact ⟨E, hE, L, e, hweil, hL, hIJ, hint, hnormal, hproj, hdim, hfin, hflat, hsurj,
    OriginalCartierRamificationSmooth.regularPoints_of_smooth_base_and_branch
      S E hE L e h2 hred hne hsm⟩

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_regular_quadratic_surface_of_nonempty_disjoint_even_selection
