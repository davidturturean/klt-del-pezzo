import KltDP.Geometry.SmoothSelectedPrimeQuadraticIntegral
import KltDP.Geometry.OriginalCartierQuadraticSurface

/-!
# A normal projective original cover from the manuscript's even selection

A nonempty finite selection of actual prime curves on the original smooth
surface and its integral Picard half-class give the original Cartier data
and original square-root cover. The actual canonical branch ideal equals
the vanishing ideal of the selected union. Its reducedness and nonemptiness
are derived here from that equality and the actual selected curves.

The previous actual-cover producers then give an integral normal projective
surface of dimension two with a finite flat surjective map to the original
surface. Every conclusion refers to the unchanged original fromSquareRoot
cover. There is no reducedness, valuation, local-coordinate, or geometric
cover premise. Smoothness of the ambient cover at the branch is separate.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance smoothSelectedPrimeQuadraticSurfaceSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance smoothSelectedPrimeQuadraticSurfaceMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- The actual even curve selection produces the same normal projective finite flat cover. -/
theorem exists_normal_projective_quadratic_cover_of_nonempty_even_selection
    (N : Finset S.PrimeCurve) (hN : N.Nonempty) (m : Additive S.toScheme.Pic)
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
        AlgebraicGeometry.Flat A.morphism ∧ AlgebraicGeometry.Surjective A.morphism := by
  obtain ⟨E, hE, L, e, hEweil, hL, hIJ, hint, hfin, hflat⟩ :=
    S.exists_integral_quadratic_cover_of_nonempty_even_selection N hN m heven
  let J := Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N)
  have hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued := by
    rw [hIJ]
    exact J.glued_isReduced (Scheme.IdealSheafData.vanishingIdeal_support (I := J)).symm
  have hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued := by
    rw [hIJ]
    obtain ⟨x, hx⟩ := S.selectedPrimeClosedUnion_nonempty N hN
    exact ⟨J.gluedSupportHomeomorph.symm ⟨x, hx⟩⟩
  let T := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
  refine ⟨E, hE, L, e, hEweil, hL, hIJ, hint, T.normal, T.projective,
    T.dimension_two, hfin, hflat, ?_⟩
  exact InvertibleQuadraticAtlas.fromSquareRoot_isSurjective S.toScheme L
    (cartierDivisorModule S.toScheme E) e (effectiveCartierSection S.toScheme E hE)

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_normal_projective_quadratic_cover_of_nonempty_even_selection
