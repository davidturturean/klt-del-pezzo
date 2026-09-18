import KltDP.Geometry.OriginalCartierRootZeroBranchCharts
import KltDP.Geometry.QuadraticRootZeroGlobalDescent

/-!
# The actual global map from root-zero ramification to the original branch

The original chart producers instantiate the abstract actual-atlas
descent theorem. Their base triangles and exact ranges supply the
original global map, its projection, closed immersion and surjectivity.
No global map, lift, image equality, or compatibility is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]

local instance originalCartierRootZeroBranchMapMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)

/-- The original chart maps descend to the same original global root-zero scheme. -/
def rootZeroGlobalBranchMap :
    (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalScheme ⟶
      (effectiveCartierIdealData X E hE L e).glueData.glued :=
  (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalDesc
    (effectiveCartierIdealData X E hE L e).gluedTo (rootZeroChartBranchMap X E hE L e)
    (rootZeroChartBranchMap_comp X E hE L e)

@[reassoc]
theorem rootZeroGlobalChartι_branchMap
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalChartι i ≫
      rootZeroGlobalBranchMap X E hE L e = rootZeroChartBranchMap X E hE L e i :=
  (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalChartι_desc
    (effectiveCartierIdealData X E hE L e).gluedTo _ _ i

@[reassoc]
theorem rootZeroGlobalBranchMap_toBase :
    rootZeroGlobalBranchMap X E hE L e ≫ (effectiveCartierIdealData X E hE L e).gluedTo =
      (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalι ≫
        (effectiveCartierQuadraticAtlas X E hE L e).morphism :=
  (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalDesc_toBase
    (effectiveCartierIdealData X E hE L e).gluedTo _ _

instance rootZeroGlobalBranchMap_isClosedImmersion :
    IsClosedImmersion (rootZeroGlobalBranchMap X E hE L e) :=
  (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalDesc_isClosedImmersion
    (effectiveCartierIdealData X E hE L e).gluedTo _ _

instance rootZeroGlobalBranchMap_surjective : Surjective (rootZeroGlobalBranchMap X E hE L e) :=
  (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalDesc_surjective
    (effectiveCartierIdealData X E hE L e).gluedTo _ _ (range_rootZeroChartBranchMap X E hE L e)

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.rootZeroGlobalBranchMap_toBase
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.rootZeroGlobalBranchMap_isClosedImmersion
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.rootZeroGlobalBranchMap_surjective
