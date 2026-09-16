import KltDP.Examples.FrobeniusGraphPicardClassPowerCharts
import KltDP.Examples.FrobeniusTranslatedCharts
import KltDP.Geometry.ProjectiveSpaceIntegral

/-!
# The original exponent-zero graph is an actual ruling fiber

The original projective power morphism at exponent zero is the constant
point [1:1]. Its original graph embedding therefore equals the horizontal
fiber embedding. An explicit isomorphism identifies the latter with the
scheme pullback defining the fiber of the second projection at [1:1].
This supplies an actual geometric fiber, without an assumed numerical
basis or a comparison with the previously chosen coordinate-zero ideal.

The proof reuses the pinned dominant-open equality theorem for morphisms
from a reduced scheme to a separated scheme. Only the original finite
polynomial chart is needed to identify the constant morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassZeroFiber

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
open FrobeniusGlobalGraphCompatibility FrobeniusGraphPicardClassPowerCharts
open FrobeniusTranslatedCharts

variable {k : Type u} [Field k]

private theorem polynomialPowerHom_zero :
    polynomialPowerHom (k := k) 0 =
      (Polynomial.C : k →+* Polynomial k).comp (Polynomial.evalRingHom (1 : k)) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [polynomialPowerHom_C, RingHom.comp_apply,
      Polynomial.coe_evalRingHom, Polynomial.eval_C]
  · simp only [polynomialPowerHom_X, pow_zero, RingHom.comp_apply,
      Polynomial.coe_evalRingHom, Polynomial.eval_X, map_one]

/-- The exponent-zero map of the original projective line is constant [1:1]. -/
theorem projectivePowerMorphism_zero :
    projectivePowerMorphism (k := k) 0 =
      projectiveSpaceToSpec k 1 ≫ pointMorphism (1 : k) := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : (projectiveSpace k 1).IsSeparated := projectiveLine_isSeparated
  letI : IsDominant (polynomialChartMap k 0) := by
    constructor
    apply (polynomialChartMap k 0).opensRange.isOpen.dense
    exact Set.range_nonempty _
  apply ext_of_isDominant (polynomialChartMap k 0)
  rw [polynomialChartMap_power_both, polynomialPowerHom_zero,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    polynomialChartMap_evaluation, ← Category.assoc,
    polynomialChartMap_structureMap]

/-- The original product morphism with second coordinate the fixed point [1:a]. -/
def horizontalFiberMorphism (a : k) : projectiveSpace k 1 ⟶ projectiveProduct k :=
  pullback.lift (𝟙 (projectiveSpace k 1))
    (projectiveSpaceToSpec k 1 ≫ pointMorphism a)
    (by rw [Category.id_comp, Category.assoc, pointMorphism_over_base,
      Category.comp_id])

@[reassoc]
theorem horizontalFiberMorphism_fst (a : k) :
    horizontalFiberMorphism a ≫ firstProjection = 𝟙 (projectiveSpace k 1) :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem horizontalFiberMorphism_snd (a : k) :
    horizontalFiberMorphism a ≫ secondProjection =
      projectiveSpaceToSpec k 1 ≫ pointMorphism a :=
  pullback.lift_snd _ _ _

/-- The literal scheme fiber over the original rational point [1:a]. -/
abbrev horizontalFiber (a : k) : Scheme.{u} :=
  pullback (secondProjection (k := k)) (pointMorphism a)

private theorem horizontalFiber_projection_structure (a : k) :
    (pullback.fst secondProjection (pointMorphism a) ≫ firstProjection) ≫
        projectiveSpaceToSpec k 1 =
      pullback.snd secondProjection (pointMorphism a) := by
  calc
    _ = pullback.fst secondProjection (pointMorphism a) ≫
        (firstProjection ≫ projectiveSpaceToSpec k 1) := Category.assoc _ _ _
    _ = pullback.fst secondProjection (pointMorphism a) ≫
        (secondProjection ≫ projectiveSpaceToSpec k 1) := by
      rw [show firstProjection (k := k) ≫ projectiveSpaceToSpec k 1 =
        secondProjection ≫ projectiveSpaceToSpec k 1 from pullback.condition]
    _ = (pullback.fst secondProjection (pointMorphism a) ≫ secondProjection) ≫
        projectiveSpaceToSpec k 1 := (Category.assoc _ _ _).symm
    _ = (pullback.snd secondProjection (pointMorphism a) ≫ pointMorphism a) ≫
        projectiveSpaceToSpec k 1 := by rw [pullback.condition]
    _ = _ := by rw [Category.assoc, pointMorphism_over_base, Category.comp_id]

private theorem horizontalFiber_projection_embedding (a : k) :
    (pullback.fst secondProjection (pointMorphism a) ≫ firstProjection) ≫
        horizontalFiberMorphism a =
      pullback.fst secondProjection (pointMorphism a) := by
  apply pullback.hom_ext
  · rw [Category.assoc, horizontalFiberMorphism_fst, Category.comp_id]
  · rw [Category.assoc, horizontalFiberMorphism_snd, ← Category.assoc,
      horizontalFiber_projection_structure]
    exact pullback.condition.symm

/-- The literal fiber is the original projective line with its specified embedding. -/
def horizontalFiberIso (a : k) : projectiveSpace k 1 ≅ horizontalFiber a where
  hom := pullback.lift (horizontalFiberMorphism a) (projectiveSpaceToSpec k 1)
    (horizontalFiberMorphism_snd a)
  inv := pullback.fst secondProjection (pointMorphism a) ≫ firstProjection
  hom_inv_id := by
    rw [← Category.assoc, pullback.lift_fst, horizontalFiberMorphism_fst]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      exact horizontalFiber_projection_embedding a
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact horizontalFiber_projection_structure a

@[reassoc]
theorem horizontalFiberIso_hom_fst (a : k) :
    (horizontalFiberIso a).hom ≫ pullback.fst secondProjection (pointMorphism a) =
      horizontalFiberMorphism a :=
  pullback.lift_fst _ _ _

/-- Equality of the actual original graph embedding and the actual y=1 fiber embedding. -/
theorem projectiveGraphMorphism_zero_eq_horizontalFiber :
    projectiveGraphMorphism (k := k) 0 = horizontalFiberMorphism (1 : k) := by
  apply pullback.hom_ext
  · rw [projectiveGraphMorphism_fst, horizontalFiberMorphism_fst]
  · rw [projectiveGraphMorphism_snd, horizontalFiberMorphism_snd,
      projectivePowerMorphism_zero]

/-- The original equalizer graph and the literal projection fiber are isomorphic. -/
def graphZeroFiberIso : graph (k := k) 0 ≅ horizontalFiber (1 : k) :=
  graphIsoProjectiveLine 0 ≪≫ horizontalFiberIso 1

/-- This isomorphism preserves the original closed embeddings into the product. -/
theorem graphZeroFiberIso_hom_fst :
    (graphZeroFiberIso (k := k)).hom ≫
        pullback.fst secondProjection (pointMorphism (1 : k)) = graphι 0 := by
  rw [graphZeroFiberIso, Iso.trans_hom, Category.assoc,
    horizontalFiberIso_hom_fst, ← projectiveGraphMorphism_zero_eq_horizontalFiber,
    ← graphIso_inv_ι, Iso.hom_inv_id_assoc]

end KltDP.Examples.FrobeniusGraphPicardClassZeroFiber
