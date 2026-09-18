import KltDP.Examples.FrobeniusMultiCentrePicardExceptionalSupport
import KltDP.Examples.FrobeniusMultiCentrePicardRealization
import KltDP.Examples.FrobeniusMultiCentreRealizedCurveClasses
import KltDP.Geometry.CartierPicardFiniteSupport

/-!
# Actual source Picard generation relative to the original product

The global complement argument gives an actual Cartier residual supported
on the original exceptional primes. The existing strict-exceptional class
formulas express each of those primes in the original total-transform
realization. Finite Weil support then puts the entire residual in that
same realization. The remaining base class is arbitrary and actual; no
base Picard generation statement is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentrePicardGenerationOverBase

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open PrimeCurveTransversalPoint
open FrobeniusProjectivePoints FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalPrime
open FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreExceptionalGlobalClasses
open FrobeniusMultiCentreGraphExceptionalPairing FrobeniusProjectivityProved
open FrobeniusMultiCentrePicardRealization FrobeniusMultiCentrePicardExceptionalSupport

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

/-- The original realization sends a unit exceptional vector to its actual total class. -/
theorem realization_exceptional (i : Fin n) (j : Fin (q + 1)) :
    realization q n a (FrobeniusPicard.exceptional (i, j)) =
      exceptionalClass (q + 1) n a i j :=
  FrobeniusMultiCentreRealizedCurveClasses.realization_exceptional q n a i j

/-- Every original embedded exceptional prime class lies in the actual realization range. -/
theorem exceptional_primeCartierClass_mem_range (i : Fin n) (idx : FinalIndex.{0} q) :
    cartierPicardHom (originalSource q n a ha).toScheme
      ((originalSource q n a ha).primeCurveCartier
        (multiSurfaceSurface_regularPoints (q + 1) n a ha
          (originalMultiStructureProjective k (q + 1) n a))
        (exceptionalPrimeCurveSPn q n a ha i idx
          (originalMultiStructureProjective k (q + 1) n a))) ∈ (realization q n a).range := by
  classical
  letI := exceptionalCurve_isIntegral q n a ha i idx
  have hclass := cartierPicardHom_primeCurveCartier_of_kernel
    (multiSurfaceSurface_regularPoints (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a))
    (exceptionalPrimeCurveSPn q n a ha i idx
      (originalMultiStructureProjective k (q + 1) n a))
    (exceptionalCurveι q n a i idx)
    (coe_exceptionalPrimeCurveSPn q n a ha i idx
      (originalMultiStructureProjective k (q + 1) n a))
    (exceptionalKernelLine q n a ha i idx) rfl
  have hkernel : (-Additive.ofMul (exceptionalKernelLine q n a ha i idx).toPic :
      Additive (multiSurface (q + 1) n a).Pic) ∈ (realization q n a).range := by
    cases idx with
    | inl j =>
        exact (congrArg (fun z : Additive (multiSurface (q + 1) n a).Pic =>
          z ∈ (realization q n a).range) (chainClass_SPn q n a ha i j)).mpr
          ((realization q n a).range.sub_mem
            ⟨FrobeniusPicard.exceptional (i, ⟨j.val, by omega⟩),
              realization_exceptional q n a i ⟨j.val, by omega⟩⟩
            ⟨FrobeniusPicard.exceptional (i, ⟨j.val + 1, by omega⟩),
              realization_exceptional q n a i ⟨j.val + 1, by omega⟩⟩)
    | inr x =>
        cases x
        exact (congrArg (fun z : Additive (multiSurface (q + 1) n a).Pic =>
          z ∈ (realization q n a).range) (newestClass_SPn q n a ha i)).mpr
          ⟨FrobeniusPicard.exceptional (i, Fin.last q),
            realization_exceptional q n a i (Fin.last q)⟩
  obtain ⟨v, hv⟩ := hkernel
  exact ⟨v, hv.trans hclass.symm⟩

include ha in
/-- Every original source class is a base pullback plus an original realized vector. -/
theorem exists_base_and_realization (c : Additive (multiSurface (q + 1) n a).Pic) :
    ∃ b : Additive (projectiveProduct k).Pic,
      ∃ v : FrobeniusPicard.PicardVector (q + 1) n,
        c = (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive b +
          realization q n a v := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨b, D, hD, hsupport⟩ := exists_base_and_exceptional_support q n a ha c.toMul
  have hmem : cartierPicardHom (originalSource q n a ha).toScheme D ∈
      (realization q n a).range := by
    apply (originalSource q n a ha).cartierPicardHom_mem_of_support
      (multiSurfaceSurface_regularPoints (q + 1) n a ha
        (originalMultiStructureProjective k (q + 1) n a)) D (realization q n a).range
    intro C hC
    obtain ⟨i, idx, hCi⟩ := hsupport C hC
    rw [hCi]
    exact exceptional_primeCartierClass_mem_range q n a ha i idx
  obtain ⟨v, hv⟩ := hmem
  refine ⟨Additive.ofMul b, v, ?_⟩
  exact hD.trans (congrArg (fun x : Additive (multiSurface (q + 1) n a).Pic =>
    (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
      (Additive.ofMul b) + x) hv.symm)

end KltDP.Examples.FrobeniusMultiCentrePicardGenerationOverBase
