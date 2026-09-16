import KltDP.Geometry.KernelRegularOpenLocality
import KltDP.Examples.FrobeniusTranslatedGraphCartierIdentity
import KltDP.Examples.FrobeniusMultiCentreIntegral
import KltDP.Examples.FrobeniusMultiCentreIsoOpenClasses

/-!
# The actual global strict graph as an effective Cartier divisor

On the accepted cover of the multi-centre surface, the original strict-graph
kernel is the open base change of the original projective graph or of a
translated tower's actual graph closure. The proved regular equations for
those kernels therefore supply regular equations for the global kernel.

This constructs an effective Cartier divisor whose ideal is the original
global strict-graph ideal. Its negative-divisor module is the original kernel
module, and its Picard class is the negative of that original kernel line.
The selected centres are the distinct affine points `(a i, (a i)^p)`, with
`p = q+1` prime in characteristic `p`, and each selected tower has depth `p`.

This supplies the global strict Cartier object, not the weighted exceptional
factorization or a numerical intersection formula on the multi-centre surface.
No projectivity, global graph-class identity or ideal factorization is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreGraphCartierStrict

open KltDP.Geometry KltDP.Geometry.KernelRegularOpenLocality
open FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusGraphZeroCartier
  FrobeniusGraphPicardClassIntegral FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
  FrobeniusStrictTransformClosure FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreGraphNewest FrobeniusMultiCentreCurveKernels
  FrobeniusMultiCentreIsoOpenClasses FrobeniusMultiCentreIntegral
  FrobeniusTranslatedGraphCartierIdentity FrobeniusTowerFunctionField.PlaneChartedScheme

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance strictGraphProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance strictGraphTranslatedInitialIntegral (p : ℕ) (a : k) :
    IsIntegral (translatedInitial p a).carrier := projectiveProduct_isIntegral

/-- Regular principal equations for the original equalizer graph kernel. -/
theorem graphι_kernel_locallyPrincipalRegular (p : ℕ) :
    IdealLocallyPrincipalRegular (graphι (k := k) p).ker := by
  rw [FrobeniusStrictTransformIsoProjectiveLine.graphι_eq_hom_comp,
    FrobeniusTowerTransportCurves.ker_comp_of_isIso]
  exact graphIdeal_locallyPrincipalRegular p

variable [IsAlgClosed k] (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

include ha

/-- The actual global strict-graph kernel has regular principal equations,
proved on the blowdown and cluster opens. -/
theorem multiGraphStrictKernel_locallyPrincipalRegular :
    IdealLocallyPrincipalRegular (graphStrictι (q + 1) n a).ker := by
  apply kernel_locallyPrincipalRegular_of_openCover (graphStrictι (q + 1) n a)
    (fun t : Option (Fin n) => match t with
      | none => blowdownIsoOpen q n a
      | some i => isoPreimage q n a i)
  · intro x
    rcases cluster_cover q n a ha x with h | ⟨i, hi⟩
    · exact ⟨none, h⟩
    · exact ⟨some i, hi⟩
  · intro t
    cases t with
    | none =>
      change IdealLocallyPrincipalRegular
        (pullback.fst (blowdownIsoOpen q n a).ι (graphStrictι (q + 1) n a)).ker
      rw [graphStrictι_ker_isoOpen₀ q n a]
      exact kernel_locallyPrincipalRegular_of_open_isPullback (blowdownMap q n a)
        (graphι (k := k) (q + 1)) _ _
        (IsPullback.of_hasPullback _ _) (graphι_kernel_locallyPrincipalRegular (q + 1))
    | some i =>
      letI : IsIntegral (selectedStage (q + 1) (a i) (q + 1)) :=
        instStageIsIntegral (translatedInitial (q + 1) (a i)) (q + 1)
      change IdealLocallyPrincipalRegular
        (pullback.fst (isoPreimage q n a i).ι (graphStrictι (q + 1) n a)).ker
      rw [FrobeniusStrictImageIsoOpen.graphStrictι_ker_isoOpen q n a i]
      exact kernel_locallyPrincipalRegular_of_open_isPullback (isoMap q n a i)
        (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0) _ _
        (IsPullback.of_hasPullback _ _)
        (translatedGraphKernel_locallyPrincipalRegular (q + 1) (a i) (q + 1) 0)

/-- The schematic-image ideal used to define the original strict graph
has the same proved regular equations. -/
theorem multiGraphLiftKernel_locallyPrincipalRegular :
    IdealLocallyPrincipalRegular (graphLift (q + 1) n a).ker := by
  have h := multiGraphStrictKernel_locallyPrincipalRegular q n a ha
  change IdealLocallyPrincipalRegular (graphLift (q + 1) n a).ker.gluedTo.ker at h
  rwa [Scheme.IdealSheafData.ker_gluedTo] at h

/-- The original global strict-graph kernel module is invertible. -/
theorem multiGraphStrictKernel_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := (multiSurface (q + 1) n a).ringCatSheaf)
      (schemeKernelIdeal (graphStrictι (q + 1) n a)) :=
  gluedKernel_isInvertible (graphLift (q + 1) n a).ker
    (multiGraphLiftKernel_locallyPrincipalRegular q n a ha)

/-- The ideal line is the kernel of the original global closed immersion. -/
def multiGraphStrictKernelLine : InvertibleSheaf (multiSurface (q + 1) n a) :=
  ⟨schemeKernelIdeal (graphStrictι (q + 1) n a),
    multiGraphStrictKernel_isInvertible q n a ha⟩

/-- The effective Cartier divisor of the original global strict graph. -/
def multiGraphStrictDivisor :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    CartierDivisor (multiSurface (q + 1) n a) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  exact cartierDivisorOfIdeal _ (graphLift (q + 1) n a).ker
    (multiGraphLiftKernel_locallyPrincipalRegular q n a ha)

theorem multiGraphStrictDivisor_hasRegularEquations :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    HasRegularCartierEquations _ (multiGraphStrictDivisor q n a ha) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  exact cartierDivisorOfIdeal_hasRegularEquations _ _ _

/-- The divisor's ideal data is the actual strict-graph kernel, preserving
its inclusion in the structure sheaf. -/
theorem multiGraphStrictDivisor_idealData :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    effectiveCartierIdealDataOfRegularEquations _ (multiGraphStrictDivisor q n a ha)
        (multiGraphStrictDivisor_hasRegularEquations q n a ha) =
      (graphStrictι (q + 1) n a).ker := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  exact (cartierDivisorOfIdeal_idealData _ (graphLift (q + 1) n a).ker
    (multiGraphLiftKernel_locallyPrincipalRegular q n a ha)).trans
      (graphLift (q + 1) n a).ker.ker_gluedTo.symm

/-- The negative-divisor module is the original strict-graph kernel module. -/
def multiGraphStrictDivisor_kernelIso :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    cartierDivisorModule _ (-multiGraphStrictDivisor q n a ha) ≅
      schemeKernelIdeal (graphStrictι (q + 1) n a) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  exact cartierDivisorOfIdeal_kernelIso _ (graphLift (q + 1) n a).ker
    (multiGraphLiftKernel_locallyPrincipalRegular q n a ha)

/-- The Cartier class is the negative class of the original kernel line. -/
theorem multiGraphStrictDivisor_picard :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    cartierPicardHom _ (multiGraphStrictDivisor q n a ha) =
      -Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  exact cartierDivisorOfIdeal_picard _ (graphLift (q + 1) n a).ker
    (multiGraphLiftKernel_locallyPrincipalRegular q n a ha)

/-- Its support is exactly the original global strict graph. -/
theorem multiGraphStrictDivisor_support :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    ((effectiveCartierIdealDataOfRegularEquations _ (multiGraphStrictDivisor q n a ha)
        (multiGraphStrictDivisor_hasRegularEquations q n a ha)).support :
        Set (multiSurface (q + 1) n a)) =
      Set.range (graphStrictι (q + 1) n a).base := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  rw [multiGraphStrictDivisor_idealData, Scheme.Hom.support_ker,
    (graphStrictι (q + 1) n a).isClosedEmbedding.isClosed_range.closure_eq]

end KltDP.Examples.FrobeniusMultiCentreGraphCartierStrict
