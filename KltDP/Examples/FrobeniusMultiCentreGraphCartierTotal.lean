import KltDP.Examples.FrobeniusMultiCentreGenericPoint
import KltDP.Examples.FrobeniusGraphZeroCartier
import KltDP.Geometry.SchemeKernelGluedIso
import KltDP.Geometry.CartierPullbackComparison
import KltDP.Geometry.CartierDivisorPullbackSupport

/-!
# The actual Cartier total transform of the graph on the multi-centre scheme

The accepted effective graph divisor has the negative Picard class of the
original graph kernel line. The proved generic-point preservation of the actual
`multiProjection` therefore permits its Cartier pullback to `multiSurface`.
This divisor has regular equations, represents the accepted total ideal class
`p • multiFirstFiberClass + multiSecondFiberClass`, and has support equal to the
inverse image of the original closed graph.

This is the total transform. The strict graph's global class still requires a
compatible ideal or Cartier factorization separating the exceptional terms;
local Picard equalities on the cluster cover do not supply that factorization.
No projectivity, characteristic or proposed strict-graph identity is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreGraphCartierTotal

open KltDP.Geometry KltDP.Geometry.CartierPullbackComparison
  FrobeniusProjectivePoints FrobeniusProjectiveMorphism
  FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassAffine
  FrobeniusGraphZeroCartier FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreGenericPoint

variable {k : Type u} [Field k]

/-- The regular effective divisor of the original graph represents the negative
class of its original kernel line, through the accepted glued-kernel comparison. -/
theorem graphZeroDivisor_picard (p : ℕ) :
    letI : IsIntegral (projectiveProduct k) :=
      FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
    cartierPicardHom (projectiveProduct k) (graphZeroDivisor p) =
      -Additive.ofMul (graphIdealLine p).toPic := by
  letI : IsIntegral (projectiveProduct k) :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  rw [graphZeroDivisor, cartierDivisorOfIdeal_picard]
  change -Additive.ofMul (gluedKernelLine (projectiveGraphMorphism (k := k) p).ker
      (graphIdeal_locallyPrincipalRegular p)).toPic = -Additive.ofMul (graphIdealLine p).toPic
  rw [← toPic_eq_gluedKernelLine (projectiveGraphMorphism (k := k) p) (graphIdealLine p).property]
  rfl

variable [IsAlgClosed k]

/-- The effective Cartier total transform of the original graph under the actual
projection of the multi-centre scheme. Source integrality is supplied. -/
def multiGraphTotalDivisor (p n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
    CartierDivisor (multiSurface p n a) := by
  letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
  letI : IsIntegral (projectiveProduct k) :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  letI : GenericPointPreserving (multiProjection p n a) :=
    multiProjection_genericPointPreserving p n a ha
  exact pullbackDivisor (multiProjection p n a) (graphZeroDivisor p)
    (graphZeroDivisor_hasRegularEquations p)

/-- The actual total transform has regular Cartier equations. -/
theorem multiGraphTotalDivisor_hasRegularEquations (p n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) :
    letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
    HasRegularCartierEquations (multiSurface p n a) (multiGraphTotalDivisor p n a ha) := by
  letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
  letI : IsIntegral (projectiveProduct k) :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  letI : GenericPointPreserving (multiProjection p n a) :=
    multiProjection_genericPointPreserving p n a ha
  exact pullbackDivisor_hasRegularEquations (multiProjection p n a) (graphZeroDivisor p)
    (graphZeroDivisor_hasRegularEquations p)

/-- The Cartier total transform represents the accepted total graph ideal class
on the entire multi-centre scheme. -/
theorem multiGraphTotalDivisor_picard_eq_totalIdeal (p n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) :
    letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
    cartierPicardHom (multiSurface p n a) (multiGraphTotalDivisor p n a ha) =
      -Additive.ofMul (multiGraphTotalIdealLine p n a).toPic := by
  letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
  letI : IsIntegral (projectiveProduct k) :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  letI : GenericPointPreserving (multiProjection p n a) :=
    multiProjection_genericPointPreserving p n a ha
  rw [multiGraphTotalDivisor, cartierPicardHom_pullbackDivisor_eq,
    graphZeroDivisor_picard, map_neg]
  change -Additive.ofMul (schemePicardPullbackHom (multiProjection p n a)
      (graphIdealLine p).toPic) = -Additive.ofMul (multiGraphTotalIdealLine p n a).toPic
  rw [schemePicardPullbackHom_toPic]
  rfl

/-- The actual Cartier total transform has the global ruling class `p a + b`. -/
theorem multiGraphTotalDivisor_picard (p n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) :
    letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
    cartierPicardHom (multiSurface p n a) (multiGraphTotalDivisor p n a ha) =
      p • multiFirstFiberClass p n a + multiSecondFiberClass p n a := by
  letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
  rw [multiGraphTotalDivisor_picard_eq_totalIdeal, inverse_multiGraphTotalIdeal_picard]

/-- The total transform's support is exactly the inverse image of the original
closed graph under the actual multi-centre projection. -/
theorem multiGraphTotalDivisor_support (p n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) :
    letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
    ((effectiveCartierIdealDataOfRegularEquations (multiSurface p n a)
        (multiGraphTotalDivisor p n a ha)
        (multiGraphTotalDivisor_hasRegularEquations p n a ha)).support : Set (multiSurface p n a)) =
      (multiProjection p n a).base ⁻¹' Set.range (projectiveGraphMorphism (k := k) p).base := by
  letI : IsIntegral (multiSurface p n a) := multiSurface_isIntegral p n a ha
  letI : IsIntegral (projectiveProduct k) :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  letI : GenericPointPreserving (multiProjection p n a) :=
    multiProjection_genericPointPreserving p n a ha
  change ((effectiveCartierIdealDataOfRegularEquations (multiSurface p n a)
      (pullbackDivisor (multiProjection p n a) (graphZeroDivisor p)
        (graphZeroDivisor_hasRegularEquations p))
      (pullbackDivisor_hasRegularEquations (multiProjection p n a) (graphZeroDivisor p)
        (graphZeroDivisor_hasRegularEquations p))).support : Set (multiSurface p n a)) = _
  rw [support_pullbackDivisor_eq_preimage, graphZeroDivisor_idealData]
  change (multiProjection p n a).base ⁻¹' ((projectiveGraphMorphism (k := k) p).ker.support :
      Set (projectiveProduct k)) = _
  rw [Scheme.Hom.support_ker,
    (projectiveGraphMorphism (k := k) p).isClosedEmbedding.isClosed_range.closure_eq]

end KltDP.Examples.FrobeniusMultiCentreGraphCartierTotal
