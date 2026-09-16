import KltDP.Examples.FrobeniusGraphPicardClassZeroFiber
import KltDP.Examples.FrobeniusGraphPicardClassSwap
import KltDP.Examples.FrobeniusGraphPicardClassRulingRelation
import KltDP.Geometry.SchemeConormalOpenImmersion
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# The integral graph class in terms of actual ruling ideals

The second ruling is the literal original graph at exponent zero, already
identified with the actual fiber y=1. Swapping that embedding gives the
first ruling x=1. The existing kernel transport isomorphism identifies
its actual ideal with the pullback of the original graph-zero ideal.

The two inverse ideal classes are therefore classes of actual fibers in
the original scheme Picard group. The full Cartier calculation gives
the original graph class p*a+b in that integral group. This does not yet
identify the classes after the manuscript's repeated blowups.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassFiberClasses

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassZeroFiber FrobeniusGraphPicardClassSwap
open FrobeniusGraphPicardClassRulingDivisors FrobeniusGraphPicardClassRulingRelation

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

/-- The actual x=1 embedding obtained by swapping the original y=1 graph. -/
def verticalFiberMorphism : projectiveSpace k 1 ⟶ projectiveProduct k :=
  projectiveGraphMorphism 0 ≫ (productSwapIso (k := k)).hom

@[reassoc]
theorem verticalFiberMorphism_fst :
    verticalFiberMorphism (k := k) ≫ firstProjection =
      projectiveSpaceToSpec k 1 ≫ pointMorphism (1 : k) := by
  rw [verticalFiberMorphism, Category.assoc]
  change projectiveGraphMorphism 0 ≫
    ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) = _
  rw [pullbackSymmetry_hom_comp_fst, projectiveGraphMorphism_snd,
    projectivePowerMorphism_zero]

@[reassoc]
theorem verticalFiberMorphism_snd :
    verticalFiberMorphism (k := k) ≫ secondProjection = 𝟙 (projectiveSpace k 1) := by
  rw [verticalFiberMorphism, Category.assoc]
  change projectiveGraphMorphism 0 ≫
    ((pullbackSymmetry _ _).hom ≫ pullback.snd _ _) = _
  rw [pullbackSymmetry_hom_comp_snd, projectiveGraphMorphism_fst]

instance verticalFiberMorphism_isClosedImmersion :
    IsClosedImmersion (verticalFiberMorphism (k := k)) := by
  unfold verticalFiberMorphism
  infer_instance

private def fiberSwap : horizontalFiber (1 : k) ⟶
    pullback (firstProjection (k := k)) (pointMorphism (1 : k)) :=
  pullback.map secondProjection (pointMorphism (1 : k))
    firstProjection (pointMorphism (1 : k)) (productSwapIso (k := k)).hom
    (𝟙 _) (𝟙 _)
    (by
      rw [Category.comp_id]
      exact (pullbackSymmetry_hom_comp_fst
        (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).symm)
    (by rw [Category.comp_id, Category.id_comp])

private instance fiberSwap_isIso : IsIso (fiberSwap (k := k)) := by
  unfold fiberSwap
  infer_instance

/-- The first ruling is also identified with its literal scheme pullback fiber. -/
def verticalFiberIso : projectiveSpace k 1 ≅
    pullback (firstProjection (k := k)) (pointMorphism (1 : k)) :=
  horizontalFiberIso 1 ≪≫ asIso (fiberSwap (k := k))

/-- The literal x=1 fiber has exactly the original swapped-graph embedding. -/
theorem verticalFiberIso_hom_fst :
    (verticalFiberIso (k := k)).hom ≫
        pullback.fst firstProjection (pointMorphism (1 : k)) = verticalFiberMorphism := by
  rw [verticalFiberIso, Iso.trans_hom, Category.assoc]
  change (horizontalFiberIso (1 : k)).hom ≫
    (pullback.lift _ _ _ ≫ pullback.fst firstProjection (pointMorphism (1 : k))) = _
  rw [pullback.lift_fst, ← Category.assoc, horizontalFiberIso_hom_fst,
    ← projectiveGraphMorphism_zero_eq_horizontalFiber]
  rfl

/-- The existing actual kernel comparison after the product isomorphism. -/
def verticalFiberKernelIso :
    (schemeModulePullback (productSwapIso (k := k)).inv).obj
        (schemeKernelIdeal (projectiveGraphMorphism 0)) ≅
      schemeKernelIdeal verticalFiberMorphism := by
  simpa only [verticalFiberMorphism, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] using
    schemeKernelPostcompOpenIso
      (projectiveGraphMorphism (k := k) 0 ≫ (productSwapIso (k := k)).hom)
      (productSwapIso (k := k)).inv

/-- The first fiber line has literally the actual swapped-graph kernel as its object. -/
def verticalFiberIdealLine : InvertibleSheaf (projectiveProduct k) :=
  InvertibleSheaf.ofIso
    (pullbackInvertibleSheaf (productSwapIso (k := k)).inv (graphIdealLine 0))
    verticalFiberKernelIso

theorem verticalFiberIdealLine_obj :
    (verticalFiberIdealLine (k := k)).obj = schemeKernelIdeal verticalFiberMorphism := rfl

/-- The second fiber line retains literally the actual y=1 embedding's kernel. -/
theorem graphZeroIdealLine_obj_horizontal :
    (graphIdealLine (k := k) 0).obj =
      schemeKernelIdeal (horizontalFiberMorphism (1 : k)) := by
  rw [graphIdealLine_obj, projectiveGraphMorphism_zero_eq_horizontalFiber]

theorem verticalFiberIdealLine_toPic :
    schemePicardPullbackHom (productSwapIso (k := k)).inv (graphIdealLine 0).toPic =
      verticalFiberIdealLine.toPic := by
  letI := Scheme.Modules.monoidalCategory (projectiveProduct k)
  rw [schemePicardPullbackHom_toPic]
  apply Units.ext
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨verticalFiberKernelIso⟩

/-- The divisor class of the actual fiber x=1, as the inverse of its actual ideal. -/
def firstFiberClass : Additive (projectiveProduct k).Pic :=
  -Additive.ofMul (verticalFiberIdealLine (k := k)).toPic

/-- The divisor class of the actual fiber y=1, as the inverse of its actual ideal. -/
def secondFiberClass : Additive (projectiveProduct k).Pic :=
  -Additive.ofMul (graphIdealLine (k := k) 0).toPic

theorem secondFiberClass_eq_ruling :
    secondFiberClass (k := k) =
      cartierPicardHom (projectiveProduct k) (rulingInfinityDivisor 1) := by
  simpa only [secondFiberClass, zero_nsmul, zero_add] using
    inverse_graphIdeal_picard_eq_rulings (k := k) 0

theorem firstFiberClass_eq_ruling :
    firstFiberClass (k := k) =
      cartierPicardHom (projectiveProduct k) (rulingInfinityDivisor 0) := by
  let P := schemePicardPullbackHom (productSwapIso (k := k)).inv
  calc
    _ = -Additive.ofMul (P (graphIdealLine 0).toPic) :=
      congrArg (fun c : (projectiveProduct k).Pic => -Additive.ofMul c)
        (verticalFiberIdealLine_toPic (k := k)).symm
    _ = P.toAdditive (secondFiberClass (k := k)) :=
      (map_neg P.toAdditive (Additive.ofMul (graphIdealLine 0).toPic)).symm
    _ = P.toAdditive
        (cartierPicardHom (projectiveProduct k) (rulingInfinityDivisor 1)) :=
      congrArg P.toAdditive secondFiberClass_eq_ruling
    _ = _ := congrArg Additive.ofMul (swap_inv_rulingPicard (k := k))

/-- The actual integral Picard identity for the original global graph and actual fibers. -/
theorem inverse_graphIdeal_picard_eq_actual_fibers (p : ℕ) :
    -Additive.ofMul (graphIdealLine (k := k) p).toPic =
      p • firstFiberClass + secondFiberClass := by
  rw [firstFiberClass_eq_ruling, secondFiberClass_eq_ruling]
  exact inverse_graphIdeal_picard_eq_rulings p

end KltDP.Examples.FrobeniusGraphPicardClassFiberClasses
