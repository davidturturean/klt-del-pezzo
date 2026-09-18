import KltDP.Geometry.PicardRestrictionSupportedCartier
import KltDP.Examples.FrobeniusMultiCentreExceptionalPrime
import KltDP.Examples.FrobeniusExceptionalLocusCover
import KltDP.Examples.FrobeniusMultiCentreGraphExceptionalPairing
import KltDP.Examples.FrobeniusStageZeroProjective
import KltDP.Examples.FrobeniusProjectivityProved

/-!
# Global Picard decomposition relative to the original base and exceptional support

The original multi-centre projection is an isomorphism on the complement
of its centres. Cartier extension on the regular original product supplies
a base class with the same restriction as any given source class. Their
difference has an actual Cartier representative supported on the actual
exceptional primes, by the original cluster-locus covering theorem. This
is a global class statement; local Picard equality alone is not used to
infer global equality. Base Picard generation is a subsequent input to be
proved on the original product, not a hypothesis of this result.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentrePicardExceptionalSupport

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusProjectivePoints FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalPrime
open FrobeniusExceptionalFinalConfiguration FrobeniusExceptionalLocusCover
open FrobeniusSpecialFiberSPn FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusStageZeroProjective FrobeniusStageSurface FrobeniusProjectivityProved

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

local instance original_source_integral : IsIntegral (multiSurface (q + 1) n a) :=
  multiSurface_isIntegral (q + 1) n a ha

/-- The existing actual source, with its proved projectivity. -/
abbrev originalSource : NormalProjectiveSurface k :=
  multiSurfaceSurface (q + 1) n a ha (originalMultiStructureProjective k (q + 1) n a)

/-- The original open of the product avoiding all selected centres. -/
abbrev baseComplement : (projectiveProduct k).Opens := earlierComplement (q + 1) n a

/-- Its original inverse image in the multi-centre surface. -/
abbrev sourceComplement : (multiSurface (q + 1) n a).Opens :=
  multiProjection (q + 1) n a ⁻¹ᵁ baseComplement q n a

local instance baseComplement_nonempty : Nonempty (baseComplement q n a).toScheme :=
  ⟨Classical.choice (earlierComplement_nonempty (q + 1) n a)⟩

local instance projection_restrict_isIso :
    IsIso (multiProjection (q + 1) n a ∣_ baseComplement q n a) :=
  multiProjection_restrict_isIso (q + 1) n a _ (not_mem_earlierComplement (q + 1) n a)

local instance sourceComplement_nonempty : Nonempty (sourceComplement q n a).toScheme :=
  ⟨(inv (multiProjection (q + 1) n a ∣_ baseComplement q n a)).base
    (Classical.choice (inferInstance : Nonempty (baseComplement q n a).toScheme))⟩

/-- Every original source class is a base pullback plus an actual exceptional-supported divisor. -/
theorem exists_base_and_exceptional_support (c : (multiSurface (q + 1) n a).Pic) :
    letI : IsIntegral (multiSurface (q + 1) n a) :=
      multiSurface_isIntegral (q + 1) n a ha
    ∃ b : (projectiveProduct k).Pic,
      ∃ D : CartierDivisor (multiSurface (q + 1) n a),
        Additive.ofMul c =
          (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
            (Additive.ofMul b) + cartierPicardHom (multiSurface (q + 1) n a) D ∧
        ∀ C : (originalSource q n a ha).PrimeCurve,
          (originalSource q n a ha).cartierToWeilHom D C ≠ 0 →
            ∃ i : Fin n, ∃ idx : FinalIndex.{0} q,
              C = exceptionalPrimeCurveSPn q n a ha i idx
                (originalMultiStructureProjective k (q + 1) n a) := by
  classical
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  letI := (projectiveProductSurface (k := k)).stalks_uniqueFactorizationMonoid_of_regular
    (stageSurface_regularPoints 0 (stage_zero_projective (k := k)))
  letI := (originalSource q n a ha).stalks_uniqueFactorizationMonoid_of_regular
    (multiSurfaceSurface_regularPoints (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a))
  let e := PointBlowupPicard.pullbackEquivOfIso
    (asIso (multiProjection (q + 1) n a ∣_ baseComplement q n a))
  obtain ⟨b, hb⟩ := CartierExtension.schemePicardPullbackHom_surjective
    (X := projectiveProductSurface (k := k)) (baseComplement q n a)
      (e.symm (schemePicardPullbackHom (sourceComplement q n a).ι c))
  have hcompat : schemePicardPullbackHom (sourceComplement q n a).ι
      (schemePicardPullbackHom (multiProjection (q + 1) n a) b) =
      e (schemePicardPullbackHom (baseComplement q n a).ι b) := by
    change schemePicardPullbackHom (sourceComplement q n a).ι
      (schemePicardPullbackHom (multiProjection (q + 1) n a) b) =
        schemePicardPullbackHom (multiProjection (q + 1) n a ∣_ baseComplement q n a)
          (schemePicardPullbackHom (baseComplement q n a).ι b)
    rw [← MonoidHom.comp_apply, ← schemePicardPullbackHom_comp,
      ← morphismRestrict_ι, schemePicardPullbackHom_comp, MonoidHom.comp_apply]
  have hsame : schemePicardPullbackHom (sourceComplement q n a).ι
      (schemePicardPullbackHom (multiProjection (q + 1) n a) b) =
      schemePicardPullbackHom (sourceComplement q n a).ι c := by
    exact hcompat.trans ((congrArg e hb).trans (e.apply_symm_apply _))
  have hzero : schemePicardPullbackHom (sourceComplement q n a).ι
      (c / schemePicardPullbackHom (multiProjection (q + 1) n a) b) = 1 := by
    rw [map_div, hsame]
    exact div_self' _
  obtain ⟨D, hD, hsupport⟩ :=
    PicardRestrictionSupportedCartier.exists_supported_cartier
      (X := originalSource q n a ha) (sourceComplement q n a)
      (c / schemePicardPullbackHom (multiProjection (q + 1) n a) b) hzero
  refine ⟨b, D, ?_, ?_⟩
  · have hD' : cartierPicardHom (multiSurface (q + 1) n a) D =
        Additive.ofMul (c / schemePicardPullbackHom (multiProjection (q + 1) n a) b) := hD
    have hsplit : Additive.ofMul c =
        (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive (Additive.ofMul b) +
          Additive.ofMul (c / schemePicardPullbackHom (multiProjection (q + 1) n a) b) := by
      change c = schemePicardPullbackHom (multiProjection (q + 1) n a) b *
        (c / schemePicardPullbackHom (multiProjection (q + 1) n a) b)
      exact (mul_div_cancel
        (schemePicardPullbackHom (multiProjection (q + 1) n a) b) c).symm
    exact hsplit.trans (congrArg (fun z : Additive (multiSurface (q + 1) n a).Pic =>
      (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
        (Additive.ofMul b) + z) hD'.symm)
  · intro C hC
    have hnot : C.genericPoint ∉ sourceComplement q n a :=
      fun hmem => hC (hsupport C hmem)
    have hcentre : ∃ i : Fin n,
        (multiProjection (q + 1) n a).base C.genericPoint = graphPoint (q + 1) (a i) := by
      apply Classical.byContradiction
      intro h
      apply hnot
      change (multiProjection (q + 1) n a).base C.genericPoint ∈ earlierComplement (q + 1) n a
      rw [mem_earlierComplement_iff]
      intro i hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hcentre
    have hcluster : C.genericPoint ∈ clusterLocus q n a i := hi
    rw [clusterLocus_eq_iUnion] at hcluster
    obtain ⟨idx, hidx⟩ := Set.mem_iUnion.mp hcluster
    exact ⟨i, idx, PrimeCurveComplementKernel.eq_of_genericPoint_mem C
      (exceptionalPrimeCurveSPn q n a ha i idx
        (originalMultiStructureProjective k (q + 1) n a)) hidx⟩

end KltDP.Examples.FrobeniusMultiCentrePicardExceptionalSupport
