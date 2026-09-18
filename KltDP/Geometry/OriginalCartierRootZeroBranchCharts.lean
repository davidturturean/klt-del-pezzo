import KltDP.Geometry.OriginalCartierRamificationSmooth
import KltDP.Geometry.QuadraticRootZeroChartBranchMap

/-!
# Actual root-zero charts map to the original Cartier branch scheme

The existing original branch-chart isomorphism and original root-zero
quotient isomorphism give the local maps. Their original base triangles
and precise ranges are retained when passing from the literal section
to the atlas's self-restricted section. This supplies actual maps for
global descent without an assumed chart comparison.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

open QuadraticCover TransitionUnitGluing
attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]

local instance originalCartierRootZeroBranchChartsMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)

/-- The original Cartier branch chart has exactly its original affine-open inverse image. -/
theorem range_branchChartMap (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    Set.range (branchChartMap X E hE L e i).base =
      (effectiveCartierIdealData X E hE L e).gluedTo.base ⁻¹'
        ((effectiveCartierQuadraticAtlas X E hE L e).opens i : Set X) := by
  rw [branchChartMap, Scheme.comp_base, TopCat.coe_comp,
    (effectiveCartierBranchChartIso X E hE L e i).inv.surjective.range_comp]
  exact (effectiveCartierIdealData X E hE L e).range_glueData_ι _

/-- The original root-zero chart has a base-compatible map with the precise original branch range. -/
theorem exists_rootZeroChart_branchMap
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    let A := effectiveCartierQuadraticAtlas X E hE L e
    let I := effectiveCartierIdealData X E hE L e
    ∃ f : A.rootZeroChart i ⟶ I.glueData.glued,
      f ≫ I.gluedTo = A.rootZeroChartToBase i ∧
      Set.range f.base = I.gluedTo.base ⁻¹' (A.opens i : Set X) := by
  exact (effectiveCartierQuadraticAtlas X E hE L e).exists_rootZeroChart_map i
    (branchChartMap X E hE L e i) (effectiveCartierIdealData X E hE L e).gluedTo
    (branchChartMap_toBase X E hE L e i) (range_branchChartMap X E hE L e i)

/-- The actual local map selected from the derived original-map comparison. -/
def rootZeroChartBranchMap (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    (effectiveCartierQuadraticAtlas X E hE L e).rootZeroChart i ⟶
      (effectiveCartierIdealData X E hE L e).glueData.glued :=
  (exists_rootZeroChart_branchMap X E hE L e i).choose

@[reassoc]
theorem rootZeroChartBranchMap_comp (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    rootZeroChartBranchMap X E hE L e i ≫ (effectiveCartierIdealData X E hE L e).gluedTo =
      (effectiveCartierQuadraticAtlas X E hE L e).rootZeroChartToBase i :=
  (exists_rootZeroChart_branchMap X E hE L e i).choose_spec.1

theorem range_rootZeroChartBranchMap (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    Set.range (rootZeroChartBranchMap X E hE L e i).base =
      (effectiveCartierIdealData X E hE L e).gluedTo.base ⁻¹'
        ((effectiveCartierQuadraticAtlas X E hE L e).opens i : Set X) :=
  (exists_rootZeroChart_branchMap X E hE L e i).choose_spec.2

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.exists_rootZeroChart_branchMap
