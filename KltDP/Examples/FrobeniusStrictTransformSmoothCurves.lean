import KltDP.Geometry.PrimeCurveIntersectionLocalLengthPoints
import KltDP.Geometry.ProjectiveLineIdealLineDegree
import KltDP.Geometry.PrimeCurveInclusionLift
import KltDP.Geometry.DivisorOrder
import KltDP.Examples.FrobeniusStrictTransformPrimeCurves
import KltDP.Examples.FrobeniusExceptionalEulerDegrees
import KltDP.Examples.FrobeniusExceptionalFinalConfiguration
import KltDP.Examples.FrobeniusGlobalBlowupSmooth

/-!
# The curves of the F29 table are smooth over `k`, hence have DVR stalks (BRIEF21, item 1)

Every curve of the stage-`n+1` configuration is isomorphic to `P¹` over `k` by an accepted
identification, and `P¹` is smooth over `k` (accepted `projectiveLine_structure_smoothOne`). An
isomorphism is an open immersion, hence smooth, and smoothness is stable under composition, so each
curve's structure morphism `C.toSpec` is smooth:

* `graphStrict_isSmooth_toSpec` (`B`), from the accepted `graphCurveToLine_base` and
  `graphSectionBase_eq`;
* `fiberStrict_isSmooth_toSpec` (`F̃`), from `fiberCurveToLine_base` and `fiberSectionBase_eq`;
* `oldExceptional_isSmooth_toSpec` (`C_j`), from the accepted `finalOldMap_projection`,
  `previousStrictι_comp_structure` and `between_comp_structure`;
* `exceptional_isSmooth_toSpec` (`P = E_n`), from the accepted `previousFiberι_comp_structure`.

By lane A2's BRIEF20 nonvacuity (`stalk_isDiscreteValuationRing_of_isSmooth`) each of these curves
therefore has a discrete valuation ring at every closed point, and the DVR-free local-length sum
formula `intersectionDegree_eq_sum_cartierOrderAt_of_isSmooth` applies to all of them
(`graphStrict_intersectionDegree_eq_sum`, bundled in `f29_strict_transform_curves_smooth_dvr`).

The curves are indexed by the projectivity `hproj` of stage `n+1`; with BRIEF20's
`stage_isProjective_of_literal` that hypothesis is supplied by Stacks 0C5P alone.

**Not proved here**: the rows `B · a`, `B · b`, `F̃ · a` themselves. The sum formula computes
`C.intersectionDegree D` for a *Cartier divisor* `D` on the stage; the classes `a` and `b` are
defined as inverses of pulled-back ideal lines (`firstFiberTotalClass`, `secondFiberTotalClass`) and
no accepted statement exhibits a Cartier divisor on the stage with those classes. See the record.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStrictTransformSmoothCurves

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.PrimeCurveInclusionLift KltDP.Geometry.ProjectiveLineIdealLineDegree
open FrobeniusGlobalBlowupStages FrobeniusStageSurface FrobeniusStrictTransformPrimeCurves
open FrobeniusStrictTransformFiberRows FrobeniusExceptionalEulerDegrees
open FrobeniusExceptionalFinalConfiguration FrobeniusGlobalExceptionalSuccessor
open FrobeniusPreviousStrictIsoProjectiveLine FrobeniusGlobalBlowupSmooth

variable {k : Type u} [Field k]

/-- Stalks of a prime-curve scheme are domains (the accepted `integralSchemeStalk_isDomain`; the
`IsDiscreteValuationRing` statements below need it to elaborate, and the local instance of lane A2's
BRIEF20 module does not leak through the import). -/
local instance smoothCurves_stalkIsDomain {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
    (y : C.toScheme) : IsDomain (C.toScheme.presheaf.stalk y) :=
  integralSchemeStalk_isDomain C.toScheme y

/-- The projective line is smooth over `k` (the accepted relative-dimension-one instance). -/
theorem projectiveLine_isSmooth : IsSmooth (projectiveSpaceToSpec k 1) :=
  IsSmoothOfRelativeDimension.isSmooth 1 (projectiveSpaceToSpec k 1)

/-- **Transport of smoothness to a prime curve**: if `φ : C.toScheme ⟶ G` is an isomorphism over a
smooth base morphism `g`, then `C.toSpec` is smooth. An isomorphism is an open immersion, hence
smooth, and smoothness is stable under composition. -/
theorem isSmooth_toSpec_of_iso {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
    {G : Scheme.{u}} (φ : C.toScheme ⟶ G) [IsIso φ] (g : G ⟶ Spec (CommRingCat.of k))
    (hg : IsSmooth g) (hφ : φ ≫ g = C.toSpec) : IsSmooth C.toSpec := by
  haveI := hg
  rw [← hφ]
  infer_instance

/-- The embedding of an older exceptional curve is over `k`, through lane F's identification with
`P¹` (the accepted `finalOldMap_projection`, `previousStrictι_comp_structure` and
`between_comp_structure`). No algebraic closedness is used. -/
theorem finalOldMap_comp_structure (A : PlaneChartedScheme k) (N j : ℕ) (h : j + 2 ≤ N) :
    finalOldMap A N j h ≫ (A.stage N).structureMap =
      (previousStrictIsoProjectiveLine (A.stage j)).hom ≫ projectiveSpaceToSpec k 1 := by
  have hb : between A h ≫ (A.stage j).next.next.structureMap = (A.stage N).structureMap :=
    between_comp_structure A h
  rw [← previousStrictι_comp_structure, ← finalOldMap_projection A N j h, Category.assoc, hb]

section Stage

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **`B` is smooth over `k`.** -/
theorem graphStrict_isSmooth_toSpec (m : ℕ) :
    IsSmooth (graphStrictPrimeCurve n hproj m).toSpec :=
  isSmooth_toSpec_of_iso _ (graphCurveToLine n hproj m) (projectiveSpaceToSpec k 1)
    projectiveLine_isSmooth
    (by rw [← graphSectionBase_eq (k := k) (m + (n + 1))]; exact graphCurveToLine_base n hproj m)

/-- **`F̃` is smooth over `k`.** -/
theorem fiberStrict_isSmooth_toSpec :
    IsSmooth (fiberStrictPrimeCurve n hproj).toSpec :=
  isSmooth_toSpec_of_iso _ (fiberCurveToLine n hproj) (projectiveSpaceToSpec k 1)
    projectiveLine_isSmooth
    (by rw [← fiberSectionBase_eq (k := k)]; exact fiberCurveToLine_base n hproj)

/-- **`C_j` is smooth over `k`.** -/
theorem oldExceptional_isSmooth_toSpec (j : ℕ) (h : j + 2 ≤ n + 1) :
    IsSmooth (oldExceptionalPrimeCurve n hproj j h).toSpec := by
  refine isSmooth_toSpec_of_iso _
    (inv (lift (oldExceptionalPrimeCurve n hproj j h)
        (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) rfl) ≫
      (previousStrictIsoProjectiveLine ((projectiveProductInitial (k := k)).stage j)).hom)
    (projectiveSpaceToSpec k 1) projectiveLine_isSmooth ?_
  calc (inv (lift (oldExceptionalPrimeCurve n hproj j h)
          (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) rfl) ≫
        (previousStrictIsoProjectiveLine ((projectiveProductInitial (k := k)).stage j)).hom) ≫
          projectiveSpaceToSpec k 1
      = inv (lift (oldExceptionalPrimeCurve n hproj j h)
          (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) rfl) ≫
        ((previousStrictIsoProjectiveLine ((projectiveProductInitial (k := k)).stage j)).hom ≫
          projectiveSpaceToSpec k 1) := Category.assoc _ _ _
    _ = inv (lift (oldExceptionalPrimeCurve n hproj j h)
          (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) rfl) ≫
        (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h ≫
          ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) := by
          rw [finalOldMap_comp_structure (projectiveProductInitial (k := k)) (n + 1) j h]
    _ = (inv (lift (oldExceptionalPrimeCurve n hproj j h)
          (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) rfl) ≫
          finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) ≫
        ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap :=
          (Category.assoc _ _ _).symm
    _ = (oldExceptionalPrimeCurve n hproj j h).inclusion ≫
        ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap := by
          rw [← inclusion_eq_inv_lift (oldExceptionalPrimeCurve n hproj j h)
            (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) rfl]
    _ = (oldExceptionalPrimeCurve n hproj j h).toSpec := rfl

/-- **`P = E_n` is smooth over `k`.** -/
theorem exceptional_isSmooth_toSpec :
    IsSmooth (exceptionalPrimeCurve n hproj).toSpec := by
  refine isSmooth_toSpec_of_iso _
    (inv (lift (exceptionalPrimeCurve n hproj)
        (previousFiberι ((projectiveProductInitial (k := k)).stage n)) rfl) ≫
      (previousFiberIso ((projectiveProductInitial (k := k)).stage n)).hom)
    (projectiveSpaceToSpec k 1) projectiveLine_isSmooth ?_
  calc (inv (lift (exceptionalPrimeCurve n hproj)
          (previousFiberι ((projectiveProductInitial (k := k)).stage n)) rfl) ≫
        (previousFiberIso ((projectiveProductInitial (k := k)).stage n)).hom) ≫
          projectiveSpaceToSpec k 1
      = inv (lift (exceptionalPrimeCurve n hproj)
          (previousFiberι ((projectiveProductInitial (k := k)).stage n)) rfl) ≫
        ((previousFiberIso ((projectiveProductInitial (k := k)).stage n)).hom ≫
          projectiveSpaceToSpec k 1) := Category.assoc _ _ _
    _ = inv (lift (exceptionalPrimeCurve n hproj)
          (previousFiberι ((projectiveProductInitial (k := k)).stage n)) rfl) ≫
        (previousFiberι ((projectiveProductInitial (k := k)).stage n) ≫
          ((projectiveProductInitial (k := k)).stage n).next.structureMap) := by
          rw [previousFiberι_comp_structure ((projectiveProductInitial (k := k)).stage n)]
    _ = (inv (lift (exceptionalPrimeCurve n hproj)
          (previousFiberι ((projectiveProductInitial (k := k)).stage n)) rfl) ≫
          previousFiberι ((projectiveProductInitial (k := k)).stage n)) ≫
        ((projectiveProductInitial (k := k)).stage n).next.structureMap :=
          (Category.assoc _ _ _).symm
    _ = (exceptionalPrimeCurve n hproj).inclusion ≫
        ((projectiveProductInitial (k := k)).stage n).next.structureMap := by
          rw [← inclusion_eq_inv_lift (exceptionalPrimeCurve n hproj)
            (previousFiberι ((projectiveProductInitial (k := k)).stage n)) rfl]
    _ = (exceptionalPrimeCurve n hproj).toSpec := rfl

/-! ### The payoff: DVR stalks and the local-length sum formula on these curves -/

/-- Every closed point of `B` has a discrete valuation ring as its stalk. -/
theorem graphStrict_stalk_isDiscreteValuationRing (m : ℕ)
    (y : (graphStrictPrimeCurve n hproj m).toScheme)
    (hy : IsClosed ({y} : Set (graphStrictPrimeCurve n hproj m).toScheme)) :
    IsDiscreteValuationRing
      ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.stalk y) :=
  haveI := graphStrict_isSmooth_toSpec n hproj m
  (graphStrictPrimeCurve n hproj m).stalk_isDiscreteValuationRing_of_isSmooth y hy

/-- Every closed point of `F̃` has a discrete valuation ring as its stalk. -/
theorem fiberStrict_stalk_isDiscreteValuationRing
    (y : (fiberStrictPrimeCurve n hproj).toScheme)
    (hy : IsClosed ({y} : Set (fiberStrictPrimeCurve n hproj).toScheme)) :
    IsDiscreteValuationRing ((fiberStrictPrimeCurve n hproj).toScheme.presheaf.stalk y) :=
  haveI := fiberStrict_isSmooth_toSpec n hproj
  (fiberStrictPrimeCurve n hproj).stalk_isDiscreteValuationRing_of_isSmooth y hy

/-- Every closed point of `C_j` has a discrete valuation ring as its stalk. -/
theorem oldExceptional_stalk_isDiscreteValuationRing (j : ℕ) (h : j + 2 ≤ n + 1)
    (y : (oldExceptionalPrimeCurve n hproj j h).toScheme)
    (hy : IsClosed ({y} : Set (oldExceptionalPrimeCurve n hproj j h).toScheme)) :
    IsDiscreteValuationRing
      ((oldExceptionalPrimeCurve n hproj j h).toScheme.presheaf.stalk y) :=
  haveI := oldExceptional_isSmooth_toSpec n hproj j h
  (oldExceptionalPrimeCurve n hproj j h).stalk_isDiscreteValuationRing_of_isSmooth y hy

/-- Every closed point of `P` has a discrete valuation ring as its stalk. -/
theorem exceptional_stalk_isDiscreteValuationRing
    (y : (exceptionalPrimeCurve n hproj).toScheme)
    (hy : IsClosed ({y} : Set (exceptionalPrimeCurve n hproj).toScheme)) :
    IsDiscreteValuationRing ((exceptionalPrimeCurve n hproj).toScheme.presheaf.stalk y) :=
  haveI := exceptional_isSmooth_toSpec n hproj
  (exceptionalPrimeCurve n hproj).stalk_isDiscreteValuationRing_of_isSmooth y hy

/-- **The local-length sum formula on `B`**, with no DVR hypothesis left. -/
theorem graphStrict_intersectionDegree_eq_sum (m : ℕ)
    (D : CartierDivisor (stageSurface (n + 1) hproj).toScheme)
    (hD : HasRegularCartierEquations (stageSurface (n + 1) hproj).toScheme D)
    (hC : (graphStrictPrimeCurve n hproj m).NotInSupport D hD) :
    letI : Fintype ((graphStrictPrimeCurve n hproj m).intersectionScheme D hD hC) :=
      haveI := (graphStrictPrimeCurve n hproj m).intersectionScheme_finite' D hD hC
      Fintype.ofFinite _
    letI : ∀ z : (graphStrictPrimeCurve n hproj m).intersectionScheme D hD hC,
        IsDiscreteValuationRing ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.stalk
          (((graphStrictPrimeCurve n hproj m).intersectionInclusion D hD hC).base z)) :=
      fun z => graphStrict_stalk_isDiscreteValuationRing n hproj m _
        ((graphStrictPrimeCurve n hproj m).intersectionInclusion_base_isClosed D hD hC z)
    (graphStrictPrimeCurve n hproj m).intersectionDegree D hD hC =
      ∑ z : (graphStrictPrimeCurve n hproj m).intersectionScheme D hD hC,
        (cartierOrderAt (graphStrictPrimeCurve n hproj m).toScheme
          ((graphStrictPrimeCurve n hproj m).restrictCartier D hD hC)
          (((graphStrictPrimeCurve n hproj m).intersectionInclusion D hD hC).base z)).toNat := by
  haveI := graphStrict_isSmooth_toSpec n hproj m
  letI : Fintype ((graphStrictPrimeCurve n hproj m).intersectionScheme D hD hC) :=
    haveI := (graphStrictPrimeCurve n hproj m).intersectionScheme_finite' D hD hC
    Fintype.ofFinite _
  letI : ∀ z : (graphStrictPrimeCurve n hproj m).intersectionScheme D hD hC,
      IsDiscreteValuationRing ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.stalk
        (((graphStrictPrimeCurve n hproj m).intersectionInclusion D hD hC).base z)) :=
    fun z => graphStrict_stalk_isDiscreteValuationRing n hproj m _
      ((graphStrictPrimeCurve n hproj m).intersectionInclusion_base_isClosed D hD hC z)
  exact (graphStrictPrimeCurve n hproj m).intersectionDegree_eq_sum_cartierOrderAt_of_isSmooth
    D hD hC

end Stage

end KltDP.Examples.FrobeniusStrictTransformSmoothCurves

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStageSurface
  FrobeniusStrictTransformPrimeCurves FrobeniusStrictTransformSmoothCurves

/-- **F29: the curves of the table are smooth over `k`**, hence have discrete valuation rings at
their closed points, so lane A2's DVR-free local-length sum formula applies to all of them. -/
theorem f29_strict_transform_curves_smooth (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) :
    (∀ m : ℕ, IsSmooth (graphStrictPrimeCurve n hproj m).toSpec) ∧
    IsSmooth (fiberStrictPrimeCurve n hproj).toSpec ∧
    (∀ (j : ℕ) (h : j + 2 ≤ n + 1), IsSmooth (oldExceptionalPrimeCurve n hproj j h).toSpec) ∧
    IsSmooth (exceptionalPrimeCurve n hproj).toSpec :=
  ⟨fun m => graphStrict_isSmooth_toSpec n hproj m, fiberStrict_isSmooth_toSpec n hproj,
    fun j h => oldExceptional_isSmooth_toSpec n hproj j h, exceptional_isSmooth_toSpec n hproj⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_strict_transform_curves_smooth_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) : True := by
  have _ := f29_strict_transform_curves_smooth.{u} k n hproj
  trivial

end KltDP.Examples
