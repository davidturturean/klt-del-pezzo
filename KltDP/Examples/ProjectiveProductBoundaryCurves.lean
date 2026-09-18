import KltDP.Examples.ProjectiveProductFactorialChart
import KltDP.Examples.FrobeniusRulingClassPairing
import KltDP.Examples.FrobeniusVerticalSupportFibre
import KltDP.Geometry.PrimeCurveComplementPicardKernel

/-!
# The two original zero fibers exhaust the reciprocal chart boundary

The omitted point of either projective line chart is its actual zero
rational point. Its inverse image is the actual horizontal or vertical
fiber, whose closed-immersion prime and Picard class are already proved.
The conclusion classifies actual prime curves outside the affine chart.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.ProjectiveProductBoundaryCurves

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusUnaffectedFibers
open FrobeniusGraphPicardClassZeroFiber FrobeniusGraphPicardClassSwap
open FrobeniusGraphPicardClassMixedCoordinates ProjectiveProductFiberClassInvariance
open FrobeniusVerticalSupportFibre FrobeniusStageZeroProjective FrobeniusRulingClassPairing
open ProjectiveProductFactorialChart

variable {k : Type u} [Field k]

/-- A point with original second coordinate `c` lies on the original horizontal fiber. -/
theorem mem_horizontalFiber_of_secondProjection_eq (c : k) (x : projectiveProduct k)
    (hx : secondProjection.base x = point c) :
    x ∈ Set.range (horizontalFiberMorphism c).base := by
  have hx' : x ∈ Set.range (pullback.fst secondProjection (pointMorphism c)).base := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨IsLocalRing.closedPoint k, hx.symm⟩
  obtain ⟨t, ht⟩ := hx'
  refine ⟨(horizontalFiberIso c).inv.base t, ?_⟩
  rw [← horizontalFiberIso_hom_fst c]
  change ((horizontalFiberIso c).inv ≫
    (horizontalFiberIso c).hom ≫ pullback.fst secondProjection (pointMorphism c)).base t = x
  rw [Iso.inv_hom_id_assoc]
  exact ht

/-- The corresponding first-coordinate assertion retains the original swapped fiber map. -/
theorem mem_verticalFiber_of_firstProjection_eq (c : k) (x : projectiveProduct k)
    (hx : firstProjection.base x = point c) :
    x ∈ Set.range (verticalFiberMorphismAt c).base := by
  have hs : secondProjection.base ((productSwapIso (k := k)).inv.base x) = point c := by
    change ((productSwapIso (k := k)).inv ≫ secondProjection).base x = point c
    rw [show (productSwapIso (k := k)).inv ≫ secondProjection = firstProjection from
      pullbackSymmetry_inv_comp_snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)]
    exact hx
  obtain ⟨t, ht⟩ := mem_horizontalFiber_of_secondProjection_eq c _ hs
  refine ⟨t, ?_⟩
  rw [verticalFiberMorphismAt_eq_swap, Scheme.comp_base_apply, ht]
  change ((productSwapIso (k := k)).inv ≫ (productSwapIso (k := k)).hom).base x = x
  rw [Iso.inv_hom_id]
  rfl

variable [IsAlgClosed k]

/-- Every actual prime outside the reciprocal chart is one of the two original zero fibers. -/
theorem eq_zeroFiber_of_genericPoint_not_mem
    (C : (projectiveProductSurface (k := k)).PrimeCurve)
    (hC : C.genericPoint ∉ productOpen (k := k) 1 1) :
    C = verticalPrimeCurve (0 : k) ∨ C = horizontalPrimeCurve (0 : k) := by
  have hnot : ¬ (firstProjection.base C.genericPoint ∈ chartOpen k 1 ∧
      secondProjection.base C.genericPoint ∈ chartOpen k 1) :=
    fun h => hC ((mem_reciprocalChart_iff C.genericPoint).mpr h)
  by_cases hf : firstProjection.base C.genericPoint ∈ chartOpen k 1
  · have hs := eq_point_zero_of_not_mem_chartOpen_one
      (secondProjection.base C.genericPoint) (fun h => hnot ⟨hf, h⟩)
    apply Or.inr
    apply PrimeCurveComplementKernel.eq_of_genericPoint_mem C (horizontalPrimeCurve (0 : k))
    exact mem_horizontalFiber_of_secondProjection_eq 0 C.genericPoint hs
  · have hs := eq_point_zero_of_not_mem_chartOpen_one (firstProjection.base C.genericPoint) hf
    apply Or.inl
    apply PrimeCurveComplementKernel.eq_of_genericPoint_mem C (verticalPrimeCurve (0 : k))
    exact mem_verticalFiber_of_firstProjection_eq 0 C.genericPoint hs

end KltDP.Examples.ProjectiveProductBoundaryCurves
