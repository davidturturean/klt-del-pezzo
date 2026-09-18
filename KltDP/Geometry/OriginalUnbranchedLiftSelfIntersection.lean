import KltDP.Geometry.OriginalUnbranchedPrimeSelfIntersection
import KltDP.Geometry.SplitAmbientPullbackLiftClassification

/-!
# Every original unbranched rational-curve lift has the original self-intersection

The original geometric data produces a split fiber and computes both
copy squares. The generic-point classification identifies any actual
map of the original integral curve above its inclusion with one of
those actual maps. It follows that the map is a closed immersion and
its actual prime-curve image has the original self-intersection.
This applies directly to existing coherent whole-tree component lifts,
without an additional supplied label or comparison isomorphism.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance originalUnbranchedLiftSelfIntersectionSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedLiftSelfIntersectionMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- Every actual lift of the original unbranched rational curve is a closed copy of the same square. -/
theorem original_unbranched_lift_selfIntersection
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hsm : IsSmooth
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism))
    (C : S.PrimeCurve) (eC : C.toScheme ≅ projectiveSpace k 1)
    (hdisj : Disjoint (C : Set S.toScheme)
      (Set.range (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo.base))
    (g : C.toScheme ⟶ (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme)
    (hg : g ≫ (effectiveCartierQuadraticAtlas S.toScheme E hE L e).morphism = C.inclusion) :
    let T := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
    let H := OriginalCartierRamificationSmooth.regularPoints_of_smooth_base_and_branch
      S E hE L e h2 hred hne hsm
    ∃ hclosed : IsClosedImmersion g,
      letI := hclosed
      (C.closedImage (T := T) g).selfIntersectionNumber H =
        C.selfIntersectionNumber S.regularPoints_of_isSmooth := by
  dsimp only
  obtain ⟨q, hq, hcard, hpair, hcopies⟩ :=
    S.exists_original_unbranched_prime_copies_preserving_selfIntersection
      E hE L e h2 hred hne hsm C eC hdisj
  obtain ⟨ε, rfl⟩ := SplitAmbientPullbackLiftClassification.eq_ambientCopy_of_projection
    (effectiveCartierQuadraticAtlas S.toScheme E hE L e).morphism C.inclusion q hq g hg
  refine ⟨inferInstance, ?_⟩
  exact (hcopies ε).1

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.original_unbranched_lift_selfIntersection

