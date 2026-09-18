import KltDP.Geometry.OriginalCartierRamificationSmooth
import KltDP.Geometry.SmoothClosedStalkCotangent
import KltDP.Geometry.CartierEulerPairingDegree

/-!
# Dimension and cotangent bounds on the original root-zero charts

The actual root-zero chart is isomorphic over the base to the original
Cartier branch chart, which is an open subscheme of the original Cartier
zero scheme. The existing divisor dimension theorem therefore bounds this
same chart by one. Actual smoothness of the original Cartier branch gives
the original root-zero stalk cotangent bound at each closed chart point.

No dimension, regularity, or coordinate condition on the branch chart is
supplied. This is the quotient-side input for ambient branch regularity.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace IsLocalRing
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

open QuadraticCover

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance originalCartierRootZeroDimensionSeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S
local instance originalCartierRootZeroDimensionMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E)

/-- The same original root-zero chart has dimension at most one. -/
theorem rootZeroChart_dimension_le_one
    (i : AffineOpenRefinement.Index S.toScheme L.localTrivializations.X) :
    topologicalKrullDim
      (rootZeroScheme ((effectiveCartierQuadraticAtlas S.toScheme E hE L e).sections i)) ≤ 1 := by
  let A := effectiveCartierQuadraticAtlas S.toScheme E hE L e
  let j := (rootZeroIsoBranch (A.sections i)).hom ≫ branchChartMap S.toScheme E hE L e i
  have hle := KltDP.Topology.topologicalKrullDim_le_of_isOpenEmbedding j.base j.isOpenEmbedding
  have hdim : topologicalKrullDim (effectiveCartierIdealData S.toScheme E hE L e).glueData.glued
      ≤ 1 := by
    rw [effectiveCartierIdealData_eq_ofRegularEquations S.toScheme E hE L e]
    exact S.topologicalKrullDim_effectiveCartierScheme_le_one E hE
  exact hle.trans hdim

/-- Smoothness of the original Cartier branch supplies the actual quotient stalk bound. -/
theorem rootZeroChart_cotangent_finrank_le_one
    (hsm : IsSmooth
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism))
    (i : AffineOpenRefinement.Index S.toScheme L.localTrivializations.X)
    (y : rootZeroScheme ((effectiveCartierQuadraticAtlas S.toScheme E hE L e).sections i))
    (hy : IsClosed ({y} : Set (rootZeroScheme
      ((effectiveCartierQuadraticAtlas S.toScheme E hE L e).sections i)))) :
    Module.finrank (ResidueField ((rootZeroScheme
      ((effectiveCartierQuadraticAtlas S.toScheme E hE L e).sections i)).presheaf.stalk y))
      (CotangentSpace ((rootZeroScheme
        ((effectiveCartierQuadraticAtlas S.toScheme E hE L e).sections i)).presheaf.stalk y)) ≤ 1 := by
  let A := effectiveCartierQuadraticAtlas S.toScheme E hE L e
  let σ := rootZeroι (A.sections i) ≫ toBase (A.sections i) ≫ (A.affine i).fromSpec ≫ S.structureMorphism
  letI : IsSmooth σ := rootZeroChart_isSmooth S.toScheme E hE L e S.structureMorphism hsm i
  exact SmoothClosedStalkCotangent.cotangent_finrank_le_one σ
    (rootZeroChart_dimension_le_one S E hE L e i) y hy

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.rootZeroChart_dimension_le_one
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.rootZeroChart_cotangent_finrank_le_one
