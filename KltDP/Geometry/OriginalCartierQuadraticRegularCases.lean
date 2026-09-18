import KltDP.Geometry.OriginalCartierBranchPointRegular
import KltDP.Geometry.OriginalCartierOffBranchSmooth
import KltDP.Geometry.NormalSurfaceRegularOnSmoothOpen
import KltDP.Geometry.QuadraticChartOffBranchPoint

/-!
# The two original-cover cases for closed-point regularity

Each declaration isolates a geometric inference on the actual Cartier
cover: regularity over the smooth complement, and the root-zero versus
nonvanishing-root split on an original affine chart. The actual branch
point theorem supplies regularity in the root-zero case.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

open QuadraticCover TransitionUnitGluing
attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance originalCartierRegularCasesSeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S
local instance originalCartierRegularCasesMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)

include h2 hred hne in
/-- An actual point over the original Cartier complement is regular on the same cover. -/
theorem regularPoint_of_map_mem_cartier_compl
    (a : (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme)
    (ha : (effectiveCartierQuadraticAtlas S.toScheme E hE L e).morphism.base a ∈
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).support.compl) :
    RegularPoint (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme a := by
  let A := effectiveCartierQuadraticAtlas S.toScheme E hE L e
  let T := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
  let V : S.toScheme.Opens :=
    (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).support.compl
  let U : A.scheme.Opens := A.morphism ⁻¹ᵁ V
  letI : IsSmooth (U.ι ≫ T.structureMorphism) :=
    OriginalCartierOffBranchSmooth.isSmooth_above_cartier_compl
      S.toScheme E hE L e S.structureMorphism h2
  exact T.regularPoint_of_isSmooth_on_open U ⟨a, ha⟩

include h2 hred hne in
/-- Every closed image point of an original cover chart is regular. -/
theorem regularPoint_of_closed_originalChart
    (hsm : IsSmooth
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism))
    (i : AffineOpenRefinement.Index S.toScheme L.localTrivializations.X)
    (z : (effectiveCartierQuadraticAtlas S.toScheme E hE L e).chart i)
    (hclosed : IsClosed
      ({((effectiveCartierQuadraticAtlas S.toScheme E hE L e).chartι i).base z} :
        Set (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme)) :
    RegularPoint (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme
      (((effectiveCartierQuadraticAtlas S.toScheme E hE L e).chartι i).base z) := by
  let A := effectiveCartierQuadraticAtlas S.toScheme E hE L e
  let s := res S.toScheme (le_refl (A.opens i)) (A.sections i)
  by_cases hz : root s ∈ z.asIdeal
  · obtain ⟨w, hw⟩ := (root_mem_iff_mem_range_rootZeroι s z).mp hz
    have heq : (rootZeroι s ≫ A.chartι i).base w = (A.chartι i).base z := by
      change (A.chartι i).base ((rootZeroι s).base w) = (A.chartι i).base z
      rw [hw]
    have hc : IsClosed ({(rootZeroι s ≫ A.chartι i).base w} : Set A.scheme) := by
      rwa [heq]
    have hr := regularPoint_of_closed_rootZeroChart S E hE L e h2 hred hne hsm i w hc
    change RegularPoint A.scheme ((rootZeroι s ≫ A.chartι i).base w) at hr
    rw [heq] at hr
    exact hr
  · apply regularPoint_of_map_mem_cartier_compl S E hE L e h2 hred hne ((A.chartι i).base z)
    rw [← OriginalCartierOffBranchSmooth.offBranchOpen_eq_cartier_compl S.toScheme E hE L e]
    exact A.map_mem_offBranchOpen_of_root_not_mem i z hz

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.regularPoint_of_map_mem_cartier_compl
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.regularPoint_of_closed_originalChart
