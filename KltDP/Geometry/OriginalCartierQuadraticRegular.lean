import KltDP.Geometry.OriginalCartierQuadraticRegularCases

/-!
# Every point of the original smooth-branch quadratic cover is regular

The actual original reduced nonempty branch gives the original normal
projective cover. Its non-closed points are regular by normality and the
surface dimension bound. At a closed point an original quadratic chart
separates the two cases: a vanishing root gives the actual root-zero
quotient, whose smooth branch and computed stalk kernel prove regularity;
a nonvanishing root gives the original Cartier complement, where the
same cover is already proved smooth over the original smooth base.

All cases retain the original cover and original maps. No ambient
regularity, cover geometry, local coordinate, or root-zero lifting datum
is a premise. This proves the project's `RegularPoint` predicate at every
point; a bundled `IsSmooth` assertion is a separate interface.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

open QuadraticCover TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance originalCartierQuadraticRegularSeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S
local instance originalCartierQuadraticRegularMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- All actual points of the original cover are regular, derived from the original smooth branch. -/
theorem regularPoints_of_smooth_base_and_branch
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hsm : IsSmooth
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism)) :
    ∀ y : (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme,
      RegularPoint (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme y := by
  let A := effectiveCartierQuadraticAtlas S.toScheme E hE L e
  let T := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
  letI : IsIntegral A.scheme := T.integral
  letI : NoetherianSpace A.scheme := T.projective.noetherianSpace
  intro a
  by_cases hclosed : IsClosed ({a} : Set A.scheme)
  · obtain ⟨i, z, rfl⟩ := A.charts_cover a
    exact regularPoint_of_closed_originalChart S E hE L e h2 hred hne hsm i z hclosed
  · letI : IsNoetherianRing (A.scheme.presheaf.stalk a) := T.projective.isNoetherianRing_stalk a
    exact regularPoint_of_normal_of_ringKrullDim_le_one A.scheme T.normal a
      (ringKrullDim_stalk_le_one_of_not_isClosed_singleton A.scheme T.dimension_two.le a hclosed)

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.regularPoints_of_smooth_base_and_branch
