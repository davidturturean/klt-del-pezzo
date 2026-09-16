import KltDP.Geometry.CartierPullbackKernelTransport
import KltDP.Examples.FrobeniusTowerTransportCartier
import KltDP.Examples.FrobeniusTowerTransportCurves

/-!
# The actual kernels of the translated exceptional Cartier divisors

The accepted old and newest exceptional divisors on the origin tower have
the kernels of its actual final components. Their transports along the
stage isomorphism therefore have exactly the kernels of the corresponding
original translated components. The proof uses the actual component
isomorphisms and their commuting squares, retaining equality of ideal data.

This is a statement on one selected tower over an arbitrary field. The
parameter `p` specifies its centre `(a,a^p)`; no primality, characteristic,
algebraic closure or projectivity hypothesis is used. The global
multi-centre exceptional factorization is a subsequent construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusTranslatedExceptionalCartierKernels

open KltDP.Geometry KltDP.Geometry.CartierDivisorPullbackAdd
  KltDP.Geometry.CartierPullbackKernelTransport
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusGraphPicardClassIntegral FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
  FrobeniusTowerTransport FrobeniusTowerTransportCartier FrobeniusTowerTransportCurves
  FrobeniusOldExceptionalLaterCartier FrobeniusExceptionalCartier

variable {k : Type u} [Field k]

local instance exceptionalOriginIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier := projectiveProduct_isIntegral

local instance exceptionalTranslatedInitialIntegral (p : ℕ) (a : k) :
    IsIntegral (translatedInitial p a).carrier := projectiveProduct_isIntegral

/-- The accepted origin Cartier divisor of each indexed final component. -/
def originFinalCartier (n : ℕ) :
    FinalIndex.{0} n → regularDivisors (projectiveContactStage (k := k) (n + 1))
  | .inl j => originOldFinal (n + 1) j.val (by omega)
  | .inr _ => originStepExceptional n

/-- Its ideal is the kernel of the original origin-tower component. -/
theorem originFinalCartier_idealData (n : ℕ) (idx : FinalIndex.{0} n) :
    effectiveCartierIdealDataOfRegularEquations _ (originFinalCartier (k := k) n idx).1
        (originFinalCartier n idx).2 =
      (finalComponentι (projectiveProductInitial (k := k)) n idx).ker := by
  cases idx with
  | inl j => exact oldFinalDivisor_idealData (n + 1) j.val (by omega)
  | inr _ => exact stepExceptionalDivisor_idealData n

/-- The accepted transported exceptional divisor, indexed by the actual
final-component index. -/
def translatedFinalCartier (p : ℕ) (a : k) (n : ℕ) (idx : FinalIndex.{0} n) :
    CartierDivisor (selectedStage p a (n + 1)) :=
  transportDivisorHom p a (n + 1) (originFinalCartier n idx)

theorem translatedFinalCartier_hasRegularEquations (p : ℕ) (a : k) (n : ℕ)
    (idx : FinalIndex.{0} n) :
    HasRegularCartierEquations _ (translatedFinalCartier p a n idx) :=
  pullbackDivisor_hasRegularEquations (stageTranslationIso p a (n + 1)).inv
    (originFinalCartier n idx).1 (originFinalCartier n idx).2

theorem translatedFinalCartier_inl (p : ℕ) (a : k) (n : ℕ) (j : Fin n) :
    translatedFinalCartier p a n (.inl j) =
      translatedOldFinalDivisor p a (n + 1) j.val (by omega) := rfl

theorem translatedFinalCartier_inr (p : ℕ) (a : k) (n : ℕ) :
    translatedFinalCartier p a n (.inr PUnit.unit) =
      translatedStepExceptionalDivisor p a n := rfl

/-- Each transported exceptional divisor has the actual translated
component kernel, by the original commuting isomorphism square. -/
theorem translatedFinalCartier_idealData (p : ℕ) (a : k) (n : ℕ)
    (idx : FinalIndex.{0} n) :
    effectiveCartierIdealDataOfRegularEquations _ (translatedFinalCartier p a n idx)
        (translatedFinalCartier_hasRegularEquations p a n idx) =
      (finalComponentι (translatedInitial p a) n idx).ker := by
  have sq : finalComponentι (translatedInitial p a) n idx ≫
        (stageTranslationIso p a (n + 1)).inv =
      ((translationChartedIso p a).finalComponentIso n idx).inv ≫
        finalComponentι (projectiveProductInitial (k := k)) n idx := by
    apply (cancel_mono (stageTranslationIso p a (n + 1)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← finalComponentι_translation p a n idx, Iso.inv_hom_id_assoc]
  exact pullbackIdealData_eq_kernel_of_iso (stageTranslationIso p a (n + 1)).symm
    (originFinalCartier n idx).1 (originFinalCartier n idx).2
    (finalComponentι (projectiveProductInitial (k := k)) n idx)
    (finalComponentι (translatedInitial p a) n idx)
    ((translationChartedIso p a).finalComponentIso n idx).symm sq
    (originFinalCartier_idealData n idx)

/-- Regular principal equations for every original translated final
component kernel. -/
theorem translatedFinalKernel_locallyPrincipalRegular (p : ℕ) (a : k) (n : ℕ)
    (idx : FinalIndex.{0} n) :
    IdealLocallyPrincipalRegular (finalComponentι (translatedInitial p a) n idx).ker := by
  rw [← translatedFinalCartier_idealData p a n idx]
  exact effectiveCartierIdealDataOfRegularEquations_regular _ _ _

/-- The transported divisor is the Cartier divisor of the actual kernel. -/
theorem translatedFinalCartier_eq_ofKernel (p : ℕ) (a : k) (n : ℕ)
    (idx : FinalIndex.{0} n) :
    translatedFinalCartier p a n idx =
      cartierDivisorOfIdeal _ (finalComponentι (translatedInitial p a) n idx).ker
        (translatedFinalKernel_locallyPrincipalRegular p a n idx) :=
  eq_cartierDivisorOfIdeal _ _ (translatedFinalKernel_locallyPrincipalRegular p a n idx)
    (translatedFinalCartier p a n idx) (translatedFinalCartier_hasRegularEquations p a n idx)
    (translatedFinalCartier_idealData p a n idx)

/-- The support is exactly the original translated final component. -/
theorem translatedFinalCartier_support (p : ℕ) (a : k) (n : ℕ)
    (idx : FinalIndex.{0} n) :
    ((effectiveCartierIdealDataOfRegularEquations _ (translatedFinalCartier p a n idx)
        (translatedFinalCartier_hasRegularEquations p a n idx)).support :
        Set (selectedStage p a (n + 1))) =
      Set.range (finalComponentι (translatedInitial p a) n idx).base := by
  rw [translatedFinalCartier_idealData, Scheme.Hom.support_ker,
    (finalComponentι (translatedInitial p a) n idx).isClosedEmbedding.isClosed_range.closure_eq]

end KltDP.Examples.FrobeniusTranslatedExceptionalCartierKernels
