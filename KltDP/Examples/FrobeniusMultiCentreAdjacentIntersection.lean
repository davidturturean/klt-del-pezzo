import KltDP.Examples.FrobeniusMultiCentreAdjacentCrossingIdeals
import KltDP.Examples.FrobeniusMultiCentreExceptionalSmooth
import KltDP.Examples.FrobeniusMultiCentreGraphExceptionalPairing
import KltDP.Geometry.PrimeCurveCrossingCoefficient

/-!
# Original adjacent global exceptional curves have intersection number one

The accepted single-point incidence and the produced original crossing-ideal
equality supply the local geometry. The actual exceptional curve is smooth,
so its closed-point stalk is a DVR; the actual neighbouring canonical Cartier
coefficient generates its maximal ideal. The accepted local-length theorem
therefore computes one, and the original kernel-to-Cartier/Picard adapters
identify this with the actual symmetric pairing of the embedded kernel lines.
Only the original global projectivity premise remains in the numerical API.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreAdjacentIntersection

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
  KltDP.Geometry.PrimeCurveClassPairing KltDP.Geometry.PrimeCurveTransversalPoint
  KltDP.Geometry.PrimeCurveCrossingCoefficient
open FrobeniusExceptionalChainPicard FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalPrime
  FrobeniusMultiCentreExceptionalGlobalClasses FrobeniusMultiCentreChainPicard
  FrobeniusMultiCentreChainTransversal FrobeniusMultiCentreAdjacentCrossingIdeals
  FrobeniusMultiCentreExceptionalSmooth FrobeniusMultiCentreGraphExceptionalPairing

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

set_option maxHeartbeats 800000 in
/-- The actual canonical Cartier intersection of adjacent original exceptional prime curves is one. -/
theorem adjacentPrime_intersectionNumber_one (i : Fin n) (j : Fin q) :
    (exceptionalPrimeCurveSPn q n a ha i (chainMember.{0} q j.castSucc) hproj).intersectionNumber
      ((multiSurfaceSurface (q + 1) n a ha hproj).primeCurveCartier
        (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
        (exceptionalPrimeCurveSPn q n a ha i (chainMember.{0} q j.succ) hproj)) = 1 := by
  let X := multiSurfaceSurface (q + 1) n a ha hproj
  let hreg := multiSurfaceSurface_regularPoints (q + 1) n a ha hproj
  let C := exceptionalPrimeCurveSPn q n a ha i (chainMember.{0} q j.castSucc) hproj
  let D := exceptionalPrimeCurveSPn q n a ha i (chainMember.{0} q j.succ) hproj
  letI := exceptionalCurve_isIntegral q n a ha i (chainMember.{0} q j.castSucc)
  letI := exceptionalCurve_isIntegral q n a ha i (chainMember.{0} q j.succ)
  letI : IsSmooth C.toSpec :=
    exceptionalPrime_isSmooth_toSpec q n a ha i (chainMember.{0} q j.castSucc) hproj
  obtain ⟨x, hx⟩ := support_nonempty q n a ha i j
  have hCD : (C : Set X.toScheme) ∩ D = {x} :=
    (support_subsingleton q n a (singlePoints q n a ha) i j).eq_singleton_of_mem hx
  have hxclosed : IsClosed ({x} : Set X.toScheme) := by
    rw [← hCD]
    exact C.isClosed.inter D.isClosed
  have hyclosed : ∀ (y : C.toScheme), C.inclusion.base y = x → IsClosed ({y} : Set C.toScheme) := by
    intro y hy
    have heq : C.inclusion.base ⁻¹' ({x} : Set X.toScheme) = {y} := by
      ext z
      change C.inclusion.base z = x ↔ z = y
      rw [← hy]
      exact C.inclusion.isClosedEmbedding.injective.eq_iff
    rw [← heq]
    exact hxclosed.preimage C.inclusion.continuous
  have hnot : C.NotInSupport (X.primeCurveCartier hreg D)
      (X.primeCurveCartier_hasRegularEquations hreg D) :=
    notInSupport_primeCurveCartier_of_subsingleton hreg C D (by
      rw [hCD]
      exact Set.subsingleton_singleton)
  apply intersectionNumber_primeCurveCartier_eq_one hreg C D x hnot hCD
  · intro y hy
    exact C.stalk_isDiscreteValuationRing_of_isSmooth y (hyclosed y hy)
  · intro y hy c hyc
    have hyC : C.inclusion.base y ∈ exceptionalSupport q n a i (chainMember.{0} q j.castSucc) := by
      rw [hy]
      exact hx.1
    have hyD : C.inclusion.base y ∈ exceptionalSupport q n a i (chainMember.{0} q j.succ) := by
      rw [hy]
      exact hx.2
    obtain ⟨U, hyU, hcross⟩ :=
      exists_adjacent_kernel_stalk_sum q n a ha i j (C.inclusion.base y) hyC hyD
    have hCker := PrimeCurveInclusionLift.ker_eq_vanishingIdeal C
      (exceptionalCurveι q n a i (chainMember.{0} q j.castSucc))
      (coe_exceptionalPrimeCurveSPn q n a ha i (chainMember.{0} q j.castSucc) hproj)
    have hDker := PrimeCurveInclusionLift.ker_eq_vanishingIdeal D
      (exceptionalCurveι q n a i (chainMember.{0} q j.succ))
      (coe_exceptionalPrimeCurveSPn q n a ha i (chainMember.{0} q j.succ) hproj)
    rw [hCker, hDker] at hcross
    exact restrictedCoefficient_irreducible_of_isSmooth X hreg C D y U hyU hcross
      (hyclosed y hy) c hyc

set_option maxHeartbeats 800000 in
/-- Adjacent original embedded exceptional kernel lines have symmetric intersection pairing one. -/
theorem adjacentKernel_pairing_one (i : Fin n) (j : Fin q) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (chainMember.{0} q j.castSucc)).toPic)
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (chainMember.{0} q j.succ)).toPic) = 1 := by
  let X := multiSurfaceSurface (q + 1) n a ha hproj
  let hreg := multiSurfaceSurface_regularPoints (q + 1) n a ha hproj
  let C := exceptionalPrimeCurveSPn q n a ha i (chainMember.{0} q j.castSucc) hproj
  let D := exceptionalPrimeCurveSPn q n a ha i (chainMember.{0} q j.succ) hproj
  letI := exceptionalCurve_isIntegral q n a ha i (chainMember.{0} q j.castSucc)
  letI := exceptionalCurve_isIntegral q n a ha i (chainMember.{0} q j.succ)
  have hclass := cartierPicardHom_primeCurveCartier_of_kernel hreg D
    (exceptionalCurveι q n a i (chainMember.{0} q j.succ))
    (coe_exceptionalPrimeCurveSPn q n a ha i (chainMember.{0} q j.succ) hproj)
    (exceptionalKernelLine q n a ha i (chainMember.{0} q j.succ)) rfl
  have hdegree := C.picardRestrictionDegreeHom_cartierPicardHom (X.primeCurveCartier hreg D)
  rw [hclass] at hdegree
  exact (pairing_kernelLine_left X hreg C
    (exceptionalCurveι q n a i (chainMember.{0} q j.castSucc))
    (coe_exceptionalPrimeCurveSPn q n a ha i (chainMember.{0} q j.castSucc) hproj)
    (exceptionalKernelLine q n a ha i (chainMember.{0} q j.castSucc)) rfl
    (-Additive.ofMul (exceptionalKernelLine q n a ha i (chainMember.{0} q j.succ)).toPic)).trans
      (hdegree.trans (adjacentPrime_intersectionNumber_one q n a ha hproj i j))

/-- The same actual adjacent pairing in the reverse order. -/
theorem adjacentKernel_pairing_one_symm (i : Fin n) (j : Fin q) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (chainMember.{0} q j.succ)).toPic)
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (chainMember.{0} q j.castSucc)).toPic) = 1 := by
  rw [multiPairing_symm]
  exact adjacentKernel_pairing_one q n a ha hproj i j

end KltDP.Examples.FrobeniusMultiCentreAdjacentIntersection
