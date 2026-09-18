import KltDP.Geometry.SplitPrimeCurveGeometry
import KltDP.Geometry.UnbranchedAmbientPullbackSplit
import KltDP.Geometry.OriginalCartierQuadraticRegular
import KltDP.Geometry.QuadraticOriginalGenericPoint
import KltDP.Geometry.SmoothSurfaceRegularity

/-!
# Actual unbranched rational-curve copies preserve self-intersection

The original branch-disjoint rational curve produces the actual splitting
of the unchanged quadratic cover's original categorical pullback.
Its two labeled original ambient maps give two disjoint prime curves,
each with the original curve's self-intersection and original source
scheme over k. The cover's regularity and all map comparisons are derived.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open SplitPrimeCurveImages SplitPrimeCurveCartierPullback

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance originalUnbranchedPrimeSelfIntersectionSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedPrimeSelfIntersectionMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- An original branch-disjoint rational curve has two actual disjoint copies of the same square. -/
theorem exists_original_unbranched_prime_copies_preserving_selfIntersection
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
      (Set.range (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo.base)) :
    let A := effectiveCartierQuadraticAtlas S.toScheme E hE L e
    let T := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
    let H := OriginalCartierRamificationSmooth.regularPoints_of_smooth_base_and_branch
      S E hE L e h2 hred hne hsm
    ∃ q : pullback A.morphism C.inclusion ≅ C.toScheme ⨿ C.toScheme,
      q.hom ≫ coprod.desc (𝟙 C.toScheme) (𝟙 C.toScheme) = pullback.snd A.morphism C.inclusion ∧
      SplitPrimeCurveGeometry.copyGeometry (T := T) A.morphism C q
        S.regularPoints_of_isSmooth H := by
  dsimp only
  let A := effectiveCartierQuadraticAtlas S.toScheme E hE L e
  let T := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
  let H := OriginalCartierRamificationSmooth.regularPoints_of_smooth_base_and_branch
    S E hE L e h2 hred hne hsm
  letI : IsIntegral A.scheme := T.integral
  letI : GenericPointPreserving A.morphism := A.morphism_genericPointPreserving
  letI : IsFinite A.morphism := A.morphism_isFinite
  letI : C.toScheme.IsSeparated := by
    constructor
    rw [← terminal.comp_from C.inclusion]
    infer_instance
  have h2C : IsUnit (2 : Γ(C.toScheme, ⊤)) := by
    simpa only [map_ofNat] using h2.map
      (C.toSpec.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  obtain ⟨q, hq⟩ := UnbranchedAmbientPullbackSplit.exists_split_on_rational_curve
    k E hE L e C.inclusion eC (by simpa only [C.range_inclusion] using hdisj) h2C
  refine ⟨q, hq, ?_⟩
  exact SplitPrimeCurveGeometry.copyGeometry_of_projection (T := T) A.morphism C q
    S.regularPoints_of_isSmooth H hq rfl

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_original_unbranched_prime_copies_preserving_selfIntersection

