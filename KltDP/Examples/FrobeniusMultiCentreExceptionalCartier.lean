import KltDP.Geometry.CartierPullbackKernelIsoLocus
import KltDP.Examples.FrobeniusTranslatedExceptionalCartierKernels
import KltDP.Examples.FrobeniusMultiCentreGenericPoint
import KltDP.Examples.FrobeniusMultiCentreExceptionalGlobalClasses

/-!
# The actual exceptional Cartier divisors on the multi-centre surface

Pull back each selected tower's actual final-component Cartier divisor
along the original tower projection. The component lies in the accepted
isomorphism locus, so the pulled divisor has exactly the kernel of the
original global exceptional closed immersion. Its negative-divisor module
is identified with that original kernel, compatibly with the inclusions.

This supplies actual global Cartier representatives for the accepted old
and newest exceptional Picard rows. Algebraic closure and injectivity of
the selected parameters are explicit. No primality, characteristic,
projectivity, degree or intersection hypothesis is used. The weighted
global graph factorization and numerical intersection results are separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreExceptionalCartier

open KltDP.Geometry KltDP.Geometry.CartierPullbackKernelIsoLocus
open FrobeniusGraphPicardClassIntegral FrobeniusTranslatedCharts
  FrobeniusContactTowerSelectedPoint FrobeniusExceptionalFinalConfiguration
  FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphNewest
  FrobeniusMultiCentreIntegral FrobeniusMultiCentreGenericPoint
  FrobeniusMultiCentreExceptionalGlobalClasses FrobeniusTranslatedExceptionalCartierKernels

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance globalExceptionalInitialIntegral (p : ℕ) (a : k) :
    IsIntegral (translatedInitial p a).carrier := projectiveProduct_isIntegral

variable [IsAlgClosed k] (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  (i : Fin n)

include ha

/-- The Cartier pullback of the selected tower's actual final component
along the original global tower projection. -/
def multiExceptionalDivisor (idx : FinalIndex.{0} q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    CartierDivisor (multiSurface (q + 1) n a) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : GenericPointPreserving (towerProjection (q + 1) n a i) :=
    towerProjection_genericPointPreserving q n a ha i
  exact pullbackDivisor (towerProjection (q + 1) n a i)
    (translatedFinalCartier (q + 1) (a i) q idx)
    (translatedFinalCartier_hasRegularEquations (q + 1) (a i) q idx)

theorem multiExceptionalDivisor_hasRegularEquations (idx : FinalIndex.{0} q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    HasRegularCartierEquations _ (multiExceptionalDivisor q n a ha i idx) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : GenericPointPreserving (towerProjection (q + 1) n a i) :=
    towerProjection_genericPointPreserving q n a ha i
  exact pullbackDivisor_hasRegularEquations _ _ _

/-- The pulled Cartier ideal is the kernel of the original global
exceptional closed immersion, as embedded ideal sheaf data. -/
theorem multiExceptionalDivisor_idealData (idx : FinalIndex.{0} q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    effectiveCartierIdealDataOfRegularEquations _ (multiExceptionalDivisor q n a ha i idx)
        (multiExceptionalDivisor_hasRegularEquations q n a ha i idx) =
      (exceptionalCurveι q n a i idx).ker := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : GenericPointPreserving (towerProjection (q + 1) n a i) :=
    towerProjection_genericPointPreserving q n a ha i
  exact pullbackIdealData_eq_kernel_of_isoLocus (towerProjection (q + 1) n a i)
    (translatedFinalCartier (q + 1) (a i) q idx)
    (translatedFinalCartier_hasRegularEquations (q + 1) (a i) q idx)
    (finalComponentι (translatedInitial (q + 1) (a i)) q idx) (isoOpen q n a i)
    (finalComponent_range_subset_isoOpen q n a ha i idx)
    (translatedFinalCartier_idealData (q + 1) (a i) q idx)

/-- The original global exceptional kernel has regular principal equations. -/
theorem multiExceptionalKernel_locallyPrincipalRegular (idx : FinalIndex.{0} q) :
    IdealLocallyPrincipalRegular (exceptionalCurveι q n a i idx).ker := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  rw [← multiExceptionalDivisor_idealData q n a ha i idx]
  exact effectiveCartierIdealDataOfRegularEquations_regular _ _ _

/-- The pulled divisor is the Cartier divisor of the actual global kernel. -/
theorem multiExceptionalDivisor_eq_ofKernel (idx : FinalIndex.{0} q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    multiExceptionalDivisor q n a ha i idx =
      cartierDivisorOfIdeal _ (exceptionalCurveι q n a i idx).ker
        (multiExceptionalKernel_locallyPrincipalRegular q n a ha i idx) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  exact eq_cartierDivisorOfIdeal _ _ (multiExceptionalKernel_locallyPrincipalRegular q n a ha i idx)
    (multiExceptionalDivisor q n a ha i idx) (multiExceptionalDivisor_hasRegularEquations q n a ha i idx)
    (multiExceptionalDivisor_idealData q n a ha i idx)

/-- The negative-divisor module is the original global exceptional kernel. -/
def multiExceptionalDivisor_kernelIso (idx : FinalIndex.{0} q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    cartierDivisorModule _ (-multiExceptionalDivisor q n a ha i idx) ≅
      schemeKernelIdeal (exceptionalCurveι q n a i idx) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  let I := effectiveCartierIdealDataOfRegularEquations _ (multiExceptionalDivisor q n a ha i idx)
    (multiExceptionalDivisor_hasRegularEquations q n a ha i idx)
  exact effectiveCartierKernelIso _ (multiExceptionalDivisor q n a ha i idx)
      (multiExceptionalDivisor_hasRegularEquations q n a ha i idx) ≪≫
    kernelIsoOfKerEq I.gluedTo (exceptionalCurveι q n a i idx)
      (I.ker_gluedTo.trans (multiExceptionalDivisor_idealData q n a ha i idx))

/-- The module comparison preserves the normalized negative-divisor
inclusion and the original exceptional kernel inclusion. -/
theorem multiExceptionalDivisor_kernelIso_inclusion (idx : FinalIndex.{0} q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    (multiExceptionalDivisor_kernelIso q n a ha i idx).hom ≫
        schemeKernelIdealι (exceptionalCurveι q n a i idx) =
      effectiveCartierNegativeInclusion _ (multiExceptionalDivisor q n a ha i idx)
        (multiExceptionalDivisor_hasRegularEquations q n a ha i idx) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  simp only [multiExceptionalDivisor_kernelIso, Iso.trans_hom, Category.assoc, schemeKernelIdealι]
  rw [kernelIsoOfKerEq_hom_ι]
  exact effectiveCartierKernelIso_hom_ι _ _ _

/-- The Cartier class is the negative class of the accepted original
global exceptional kernel line. -/
theorem multiExceptionalDivisor_picard (idx : FinalIndex.{0} q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    cartierPicardHom _ (multiExceptionalDivisor q n a ha i idx) =
      -Additive.ofMul (exceptionalKernelLine q n a ha i idx).toPic := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  rw [multiExceptionalDivisor_eq_ofKernel, cartierDivisorOfIdeal_picard,
    ← toPic_eq_gluedKernelLine (exceptionalCurveι q n a i idx)
      (exceptionalKernel_isInvertible q n a ha i idx)
      (multiExceptionalKernel_locallyPrincipalRegular q n a ha i idx)]
  rfl

/-- The actual Cartier representative of the accepted global old-component row. -/
theorem multiExceptionalDivisor_picard_inl (j : Fin q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    cartierPicardHom _ (multiExceptionalDivisor q n a ha i (.inl j)) =
      exceptionalClass (q + 1) n a i ⟨j.val, by omega⟩ -
        exceptionalClass (q + 1) n a i ⟨j.val + 1, by omega⟩ := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  rw [multiExceptionalDivisor_picard]
  exact chainClass_SPn q n a ha i j

/-- The actual Cartier representative of the accepted global newest-component row. -/
theorem multiExceptionalDivisor_picard_inr :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    cartierPicardHom _ (multiExceptionalDivisor q n a ha i (.inr PUnit.unit)) =
      exceptionalClass (q + 1) n a i (Fin.last q) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  rw [multiExceptionalDivisor_picard]
  exact newestClass_SPn q n a ha i

/-- The support is the original global exceptional closed subscheme. -/
theorem multiExceptionalDivisor_support (idx : FinalIndex.{0} q) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    ((effectiveCartierIdealDataOfRegularEquations _ (multiExceptionalDivisor q n a ha i idx)
        (multiExceptionalDivisor_hasRegularEquations q n a ha i idx)).support :
        Set (multiSurface (q + 1) n a)) =
      Set.range (exceptionalCurveι q n a i idx).base := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  rw [multiExceptionalDivisor_idealData, Scheme.Hom.support_ker,
    (exceptionalCurveι q n a i idx).isClosedEmbedding.isClosed_range.closure_eq]

end KltDP.Examples.FrobeniusMultiCentreExceptionalCartier
