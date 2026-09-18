import KltDP.Examples.FrobeniusFiberZeroInvertible
import KltDP.Examples.FrobeniusGraphPicardClassMixedCoordinates
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The actual product chart has a factorial section ring

The original four-chart cover has polynomial-plane sources. The original
open-immersion section isomorphism and Spec global-section isomorphism
transfer unique factorization to the actual section ring on the product.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.ProjectiveProductFactorialChart

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusBlowupContact FrobeniusGraphClosed
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassMixedCoordinates FrobeniusFiberZeroInvertible

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

/-- The original chart section-ring equivalence, without any chosen affine model. -/
def sectionEquiv (i j : Fin 2) :
    planeRing k ≃+* Γ(projectiveProduct k, productOpen i j) :=
  (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).symm.commRingCatIsoToRingEquiv.trans
    ((productChart (k := k) i j).appIso ⊤).symm.commRingCatIsoToRingEquiv

/-- Each original product chart is affine. -/
theorem productOpen_isAffineOpen (i j : Fin 2) :
    IsAffineOpen (productOpen (k := k) i j) :=
  (fiberChartAffineOpen (k := k) i j).2

/-- Unique factorization holds in the actual section ring. -/
theorem sections_uniqueFactorizationMonoid (i j : Fin 2) :
    UniqueFactorizationMonoid Γ(projectiveProduct k, productOpen i j) :=
  (sectionEquiv (k := k) i j).toMulEquiv.uniqueFactorizationMonoid inferInstance

/-- Membership in the original reciprocal chart means both coordinates are in chart one. -/
theorem mem_reciprocalChart_iff (x : projectiveProduct k) :
    x ∈ productOpen (k := k) 1 1 ↔
      (firstProjection (k := k)).base x ∈ ProjectiveLineComparison.chartOpen k 1 ∧
        (secondProjection (k := k)).base x ∈ ProjectiveLineComparison.chartOpen k 1 := by
  rw [productOpen, Scheme.Hom.image_top_eq_opensRange]
  change x ∈ Set.range (productChart (k := k) 1 1).base ↔ _
  rw [productChart_range]
  rfl

end KltDP.Examples.ProjectiveProductFactorialChart
