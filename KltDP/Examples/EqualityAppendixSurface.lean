import KltDP.Examples.FrobeniusMultiCentreGraphFiber
import KltDP.Examples.EqualityAppendixPullbackProjection
import KltDP.Examples.FrobeniusContactTowerInfinity

/-!
# The appendix's original contact towers at zero, one, and infinity

The third tower is built in the original reciprocal chart. It is not a
finite-centre model identified through an unproved coordinate change.
The projection is an isomorphism away from the three specified centres.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.EqualityAppendixSurface

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusMultiCentreSurface
  FrobeniusContactTowerInfinity FrobeniusStageComplement.PlaneChartedScheme

variable {k : Type u} [Field k] [CharP k 3]

def finiteParameters : Fin 2 → k := ![0, 1]

/-- The two original finite towers, each with three contact blowups. -/
abbrev finiteSurface : Scheme.{u} := multiSurface 3 2 (finiteParameters (k := k))

def finiteProjection : finiteSurface (k := k) ⟶ projectiveProduct k :=
  multiProjection 3 2 finiteParameters

/-- The actual product of the original towers at `0`, `1`, and `∞`. -/
abbrev surface : Scheme.{u} :=
  pullback (finiteProjection (k := k)) (infinityProjection 3)

def projection : surface (k := k) ⟶ projectiveProduct k :=
  pullback.fst finiteProjection (infinityProjection 3) ≫ finiteProjection

def structureMap : surface (k := k) ⟶ Spec (CommRingCat.of k) :=
  projection ≫ projectiveProductToSpec

instance finiteProjection_isProper : IsProper (finiteProjection (k := k)) :=
  multiProjection_isProper 3 2 finiteParameters

instance projection_isProper : IsProper (projection (k := k)) :=
  EqualityAppendixPullbackProjection.proper finiteProjection (infinityProjection 3)

instance structureMap_isProper : IsProper (structureMap (k := k)) := by
  unfold structureMap
  infer_instance

/-- The original product with exactly the three selected centres removed. -/
def centersComplement : (projectiveProduct k).Opens :=
  earlierComplement 3 2 finiteParameters ⊓ initialPuncture (infinityInitial k)

theorem finiteProjection_restrict_isIso :
    IsIso (finiteProjection (k := k) ∣_ centersComplement) := by
  apply multiProjection_restrict_isIso
  intro i hi
  exact not_mem_earlierComplement 3 2 finiteParameters i hi.1

theorem infinityProjection_restrict_isIso :
    IsIso (infinityProjection (k := k) 3 ∣_ centersComplement) := by
  letI : IsIso (infinityProjection (k := k) 3 ∣_ initialPuncture (infinityInitial k)) :=
    toInitial_restrict_isIso (infinityInitial k) 3
  exact FrobeniusStageComplement.restrict_isIso_of_le (infinityProjection 3)
    (show centersComplement (k := k) ≤ initialPuncture (infinityInitial k) from inf_le_right)

/-- The literal combined blowdown is an isomorphism off the three centres. -/
theorem projection_restrict_isIso :
    IsIso (projection (k := k) ∣_ centersComplement) := by
  letI := finiteProjection_restrict_isIso (k := k)
  letI := infinityProjection_restrict_isIso (k := k)
  exact EqualityAppendixPullbackProjection.restrict_isIso
    (finiteProjection (k := k)) (infinityProjection 3) centersComplement

end KltDP.Examples.EqualityAppendixSurface
