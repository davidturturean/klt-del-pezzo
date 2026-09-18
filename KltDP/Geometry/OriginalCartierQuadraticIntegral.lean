import KltDP.Geometry.CartierQuadraticBranchCharts
import KltDP.Geometry.EffectiveCartierIdeal

/-!
# Integrality of the original cover with nonempty reduced Cartier branch

The original Cartier zero scheme supplies a point in an actual affine
chart of the original half-line atlas. Its actual chart isomorphism
transfers reducedness to the literal quadratic branch quotient. The
canonical Cartier section is already proved nonzero, so the existing
nonsquare argument proves integrality of the same original cover.

Only normality of the integral base and nonemptiness and reducedness of
the original Cartier zero scheme are required. No branch-chart point,
valuation, local coordinate, nonsquare coefficient, or cover integrality
is supplied. In particular the theorem applies to a nonempty smooth
reduced branch without a characteristic restriction for integrality.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalCartierQuadraticIntegral

open QuadraticCover InvertibleQuadraticAtlas

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]

local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

variable (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)

/-- Global reducedness of the original Cartier zero scheme gives the literal branch quotient. -/
theorem branchChart_isReduced
    (hred : IsReduced (effectiveCartierIdealData X E hE L e).glueData.glued)
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    IsReduced (branchScheme ((effectiveCartierQuadraticAtlas X E hE L e).sections i)) := by
  let A := effectiveCartierQuadraticAtlas X E hE L e
  let I := effectiveCartierIdealData X E hE L e
  letI : IsReduced I.glueData.glued := hred
  letI : IsReduced (I.glueDataObj ⟨A.opens i, A.affine i⟩) :=
    isReduced_of_isOpenImmersion (I.glueData.ι ⟨A.opens i, A.affine i⟩)
  exact isReduced_of_isOpenImmersion (effectiveCartierBranchChartIso X E hE L e i).inv

/-- A point of the original Cartier zero scheme supplies a point of an original branch chart. -/
theorem exists_nonempty_branchChart
    (hne : Nonempty (effectiveCartierIdealData X E hE L e).glueData.glued) :
    ∃ i : AffineOpenRefinement.Index X L.localTrivializations.X,
      Nonempty (branchScheme ((effectiveCartierQuadraticAtlas X E hE L e).sections i)) := by
  let A := effectiveCartierQuadraticAtlas X E hE L e
  let I := effectiveCartierIdealData X E hE L e
  let y : I.glueData.glued := Classical.choice hne
  have hy : I.gluedTo.base y ∈ ⨆ i, A.opens i := by
    rw [A.covers]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  have hm : y ∈ Set.range (I.glueData.ι ⟨A.opens i, A.affine i⟩).base := by
    rw [I.range_glueData_ι]
    exact hi
  obtain ⟨z, _hz⟩ := hm
  exact ⟨i, ⟨(effectiveCartierBranchChartIso X E hE L e i).hom.base z⟩⟩

/-- The exact original square-root cover is integral from the original reduced Cartier branch. -/
theorem scheme_isIntegral_of_reduced_nonempty_branch (hnormal : IsNormalScheme X)
    (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations X E hE).glueData.glued)
    (hne : Nonempty (effectiveCartierIdealDataOfRegularEquations X E hE).glueData.glued) :
    IsIntegral (fromSquareRoot X L (cartierDivisorModule X E) e
      (effectiveCartierSection X E hE)).scheme := by
  have hred' : IsReduced (effectiveCartierIdealData X E hE L e).glueData.glued := by
    rw [effectiveCartierIdealData_eq_ofRegularEquations X E hE L e]
    exact hred
  have hne' : Nonempty (effectiveCartierIdealData X E hE L e).glueData.glued := by
    rw [effectiveCartierIdealData_eq_ofRegularEquations X E hE L e]
    exact hne
  obtain ⟨i, ⟨y⟩⟩ := exists_nonempty_branchChart X E hE L e hne'
  exact fromSquareRoot_scheme_isIntegral_of_reduced_branch X hnormal L
    (cartierDivisorModule X E) e (effectiveCartierSection X E hE)
    (effectiveCartierSection_ne_zero X E hE) i y
    (branchChart_isReduced X E hE L e hred' i)

end KltDP.Geometry.OriginalCartierQuadraticIntegral

#print axioms KltDP.Geometry.OriginalCartierQuadraticIntegral.scheme_isIntegral_of_reduced_nonempty_branch
